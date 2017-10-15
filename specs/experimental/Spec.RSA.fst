module Spec.RSA

open FStar.Seq
open FStar.Mul
open FStar.UInt
open FStar.Math.Lemmas
open Spec.SHA2_256
open Spec.Seq.Lib
open Spec.Bignum
open Spec.Bignum.Lib

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

(* PREREQUISITES *)

(* SHA256 *)
let max_input_len_sha256 = pow2 61
unfold let hLen = 32ul
val hash_sha256:
	msg:bytes{length msg < max_input_len_sha256} -> 
	hash:lbytes hLen ->
	Tot (msgHash:lbytes hLen)
let hash_sha256 msg h = SHA2_256.hash msg

(* RSA *)
type modBits = modBits:U32.t{U32.v modBits > 0}

type rsa_pubkey (modBits:modBits) =
	| Mk_rsa_pubkey: n:pos{n < pow2 (U32.v modBits)} -> e:elem n -> rsa_pubkey modBits
	
type rsa_privkey (modBits:modBits) =
	| Mk_rsa_privkey: pkey:rsa_pubkey modBits -> d:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey modBits

#reset-options "--z3rlimit 50"

(* USE MONTGOMERY INVERSE METHOD *)
(* a*x + b*y = gcd(a,b) *)
val extended_eucl: a:bignum -> b:bignum -> Tot (tuple2 int int) (decreases b)
let rec extended_eucl a b =
	if b = 0 then (1, 0)
	else
		match (extended_eucl b (bignum_mod a b)) with
		| (x, y) -> (y, bignum_sub x (bignum_mul (bignum_div a b) y))

val mod_exp_loop: n:pos -> a:bignum -> b:bignum -> acc:elem n -> Tot (res:elem n) (decreases b)
let rec mod_exp_loop n a b acc =
	match b with
	| 0 -> acc
	| 1 -> bignum_mul_mod a acc n
	| e ->
		let a2 = bignum_mul_mod a a n in
		let acc =
			if (bignum_is_even e) then acc
			else bignum_mul_mod a acc n in
		mod_exp_loop n a2 (bignum_div2 b) acc

val mod_exp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n)
let mod_exp n a b =
	let one_n = 1 % n in
	mod_exp_loop n a b one_n

(*
val pow: a:bignum -> n:bignum -> Tot bignum (decreases n)
let rec pow a n =
	match n with
	| 0 -> 1
	| _ -> 
		let b = pow a (n/2) in
		op_Multiply b (op_Multiply b (if n % 2 = 0 then 1 else a))

val fexp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n) 
let fexp n a b = (pow a b) % n
*)

val mgf_sha256_loop:
	mgfseed:bytes{length mgfseed = (U32.v hLen) + 4} ->
        counter_max:UInt32.t ->
	acc:bytes{length acc = U32.v counter_max * U32.v hLen /\ length acc < pow2 32} ->
	Tot (res:bytes{length res = length acc})

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

let mgf_sha256_loop mgfseed counter_max acc =
    let mHash = create hLen 0uy in
    let accLen = seq_length acc in
    let acc: lbytes accLen = acc in
    let next (acc:lbytes accLen) (i:U32.t{U32.v i < U32.v counter_max}) : lbytes accLen =
    	let mgfseed = update_slice mgfseed hLen 4ul (store32_be i) in
		let mHash = hash_sha256 mgfseed mHash in
		blit mHash 0ul acc (hLen *^ i) hLen in
    for_loop #(lbytes accLen) 0ul counter_max next acc

(* We only allow U32.t masklen, this means that we always have the property
   that maskLen <= op_Multiply (pow2 32) (U32.v hLen) as required by the spec *)
val mgf_sha256:
	mgfseed:bytes{length mgfseed = U32.v hLen + 4} ->
	maskLen:U32.t{U32.v maskLen > 0 /\ U32.v (blocks maskLen hLen) * U32.v hLen < pow2 32} ->
	mask:bytes{length mask = U32.v maskLen} ->
	Tot (mask':bytes{length mask = U32.v maskLen})

let mgf_sha256 mgfseed maskLen mask =
	let counter_max = blocks maskLen hLen in
	let accLen =  counter_max *^ hLen in
	let acc = create accLen 0x00uy in
	let acc = mgf_sha256_loop mgfseed counter_max acc in
	slice acc 0ul maskLen

val pss_encode_:
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	emLen:U32.t{U32.v emLen - length salt - U32.v hLen - 2 >= 0} ->
	em:lbytes emLen ->
	Tot (em':lbytes emLen)

let pss_encode_ salt msg emLen em =
	let mHash = create hLen 0uy in
	let mHash = hash_sha256 msg mHash in

	let sLen = seq_length salt in
	let emLen = seq_length em in

	let m1_size = 8ul +^ hLen +^ sLen in
	let m1 = create m1_size 0x00uy in
	let m1 = blit mHash 0ul m1 8ul hLen in
	let m1 = blit salt 0ul m1 (8ul +^ hLen) sLen in
	let m1Hash = create 36ul 0uy in
	let m1Hash = update_slice m1Hash 0ul hLen (hash_sha256 m1) in
	
	let db_size = emLen -^ hLen -^ 1ul in
	let db = create db_size 0x00uy in
	let last_before_salt = db_size -^ sLen -^ 1ul in
	let db = db.[last_before_salt] <- 0x01uy in
	let db = blit salt 0ul db (last_before_salt +^ 1ul) sLen in

    let dbMask = create db_size 0uy in
	let dbMask = mgf_sha256 m1Hash db_size dbMask in
	let maskedDB = xor_bytes db dbMask in

	let em = blit maskedDB 0ul em 0ul db_size in
	let em = blit m1Hash 0ul em db_size hLen in
    upd em (emLen -^ 1ul) 0xbcuy

val pss_encode:
	msBits:U32.t{U32.v msBits < 8} ->
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32} -> 
	msg:bytes{length msg < max_input_len_sha256} ->
	em:bytes{length em - length salt - U32.v hLen - 3 >= 0} ->
	Tot (res:bytes{length res = length em})

#reset-options "--z3rlimit 100 --max_fuel 0"

let pss_encode msBits salt msg em =
	let emLen = seq_length em in
	if msBits =^ 0ul
	then update_slice em 1ul (emLen -^ 1ul) (pss_encode_ salt msg (emLen -^ 1ul))
	else 
		let em = pss_encode_ salt msg emLen em in
		em.[0ul] <- U8.(em.[0ul] &^ (0xffuy >>^ U32.(8ul -^ msBits)))

val pss_verify_:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	msBits:U32.t{U32.v msBits < 8} ->
	em:bytes{length em - U32.v sLen - U32.v hLen - 2 >= 0} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let pss_verify_ sLen msBits em msg =
	let emLen = seq_length em in
	let mHash = create hLen 0uy in
	let mHash = hash_sha256 msg mHash in

	let pad_size = emLen -^ sLen -^ hLen -^ 1ul in
	let pad2 = create pad_size 0x00uy in
	let pad2 = pad2.[pad_size -^ 1ul] <- 0x01uy in

	let db_size = emLen -^ hLen -^ 1ul in
	let maskedDB = slice em 0ul db_size in
	let m1Hash0 = slice em db_size (db_size +^ hLen) in
	let m1Hash = create 36ul 0uy in
	let m1Hash = blit m1Hash0 0ul m1Hash 0ul hLen in
	let dbMask = create db_size 0uy in
	let dbMask = mgf_sha256 m1Hash db_size dbMask in
	let db = xor_bytes maskedDB dbMask in
	let db =
		if msBits >^ 0ul
		then db.[0ul] <- U8.(db.[0ul] &^ (0xffuy >>^ U32.(8ul -^ msBits)))
		else db in
	
	let pad = slice db 0ul pad_size in
	let salt = slice db pad_size (pad_size +^ sLen) in

	let m1_size = 8ul +^ hLen +^ sLen in
	let m1 = create m1_size 0x00uy in
	if not (Seq.eq pad pad2) then false
	else begin
		(* first 8 elements should be 0x00 *)
		let m1 = blit mHash 0ul m1 8ul hLen in
		let m1 = blit salt 0ul m1 (8ul +^ hLen) sLen in
		let m1Hash' = create hLen 0uy in
		let m1Hash' = hash_sha256 m1 m1Hash' in
		Seq.eq m1Hash0 m1Hash'
	end

val pss_verify:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	msBits:U32.t{U32.v msBits < 8} ->
	em:bytes{length em > 0} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let pss_verify sLen msBits em msg =
	let emLen = seq_length em in
	let em_0 = U8.(em.[0ul] &^ (0xffuy <<^ msBits)) in
	let em_last = em.[emLen -^ 1ul] in

	if not (U8.(em_0 =^ 0x00uy) && U8.(em_last =^ 0xbcuy))
	then false
	else begin
		let em' = if msBits =^ 0ul then slice em 1ul emLen else em in
		if (seq_length em' <^ sLen +^ hLen +^ 2ul)
		then false
		else pss_verify_ sLen msBits em' msg
		end

val rsa_sign:
	modBits:modBits ->
	skey:rsa_privkey modBits ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32 /\ U32.v (blocks modBits 8ul) - length salt - U32.v hLen - 3 >= 0} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	Tot (sgnt:bytes{length sgnt = U32.v (blocks modBits 8ul)})

let rsa_sign modBits skey rBlind salt msg =
	let k = blocks modBits 8ul in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	assert(U32.v modBits <= 8 * U32.v k);
	pow2_le_compat (8 * U32.v k) (U32.v modBits);
	assert(pow2 (U32.v modBits) <= pow2 (8 * U32.v k));
	assert(n < pow2 (8 * U32.v k));

	let msBits = (modBits -^ 1ul) %^ 8ul in
	let em = create k 0x00uy in
	let em = pss_encode msBits salt msg em in
	let m = os2ip em in
	(* BLINDING *)
	let rBlind_inv, _ = extended_eucl rBlind n in
	let rBlind_e = mod_exp n rBlind e in
	let m1 = bignum_mul_mod m rBlind_e n in
	let s1 = mod_exp n m1 d in
	let s = bignum_mul_mod s1 rBlind_inv n in
	let sgnt = create k 0x00uy in
	assert(s < n);
	i2osp s sgnt

val rsa_verify:
	modBits:modBits ->
	pkey:rsa_pubkey modBits ->
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	sgnt:bytes{length sgnt = U32.v (blocks modBits 8ul)} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let rsa_verify modBits pkey sLen sgnt msg =
	let k = blocks modBits 8ul in
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in
	assert(U32.v modBits <= 8 * U32.v k);
	pow2_le_compat (8 * U32.v k) (U32.v modBits);
	assert(pow2 (U32.v modBits) <= pow2 (8 * U32.v k));
	assert(n < pow2 (8 * U32.v k));

	let s = os2ip sgnt in
	if bignum_is_less s n then begin
		let m = mod_exp n s e in
		let em = create k 0x00uy in
		let em = i2osp m em in
		let msBits = (modBits -^ 1ul) %^ 8ul in
		pss_verify sLen msBits em msg end 
	else false