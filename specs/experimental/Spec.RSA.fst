module Spec.RSA

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.SHA2_256

module U8 = FStar.UInt8
module U32 = FStar.UInt32

#set-options "--lax"

(* PREREQUISITES *)

(* SEQUENCES *)
type byte = UInt8.t
type bytes = seq byte

(* SHA256 *)
let max_input_len_sha256 = pow2 61
let hLen = 32
val hash_sha256:
	msg:bytes{length msg < max_input_len_sha256} ->
	Tot (msgHash:bytes{length msgHash = hLen})
let hash_sha256 msg = SHA2_256.hash msg

(* BIGNUM *)
type bignum = nat
type elem (n:pos) = e:bignum{e < n}
let bignum_to_uint8 x = U8.uint_to_t (to_uint_t 8 x)
let uint8_to_bignum x = U8.v x
let bignum_mul x y = (op_Multiply x y)
let bignum_mod x y = x % y
let bignum_div x y = x / y
let bignum_add x y = x + y
let bignum_sub x y = x - y
let bignum_mul_mod x y m = (x * y) % m
let bignum_is_even x = (x % 2) = 0
let bignum_div2 x = x / 2 
let bignum_one = 1

let bignum_to_uint32 x = U32.uint_to_t (to_uint_t 32 x)

(* RSA *)
type rsa_pubkey =
	| Mk_rsa_pubkey: n:pos -> e:elem n -> rsa_pubkey
	
type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey

(* a*x + b*y = gcd(a,b) *)
val extended_eucl: a:bignum -> b:bignum -> Tot (tuple2 bignum bignum) (decreases b)
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
	let one_n : elem n = 1 in
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

val os2ip: b:bytes -> Tot nat (decreases (Seq.length b))
let rec os2ip b =
	let bLen = Seq.length b in
	if bLen = 0 then 0
	else op_Multiply (U8.v (head b)) (pow2 (op_Multiply 8 (bLen - 1))) + (os2ip (tail b))

val i2osp:
	n:nat -> bLen:nat{n < pow2 (op_Multiply 8 bLen)} -> 
	Tot (b:bytes{length b = bLen}) (decreases bLen)
let rec i2osp n bLen =
	if bLen = 0 then createEmpty #UInt8.t
	else
		let len = bLen - 1 in
		let t = pow2 (op_Multiply 8 len) in
		let x = bignum_to_uint8 (n / t) in
		let n = n % t in
		append (create 1 x) (i2osp n len)

val get_octets: modBits:pos -> Tot bignum
let get_octets modBits = (modBits - 1)/8 + 1

(* the same error as in impl *)
val get_length_em: modBits:pos -> Tot bignum
let get_length_em modBits = get_octets modBits

val mgf_sha256_loop:
	mgfseed:bytes{length mgfseed = hLen} ->
	counter_max:bignum{counter_max <= pow2 32} -> counter:bignum{counter <= counter_max} ->
	acc:bytes{length acc = op_Multiply counter hLen} ->
	Tot (res:bytes{length res = op_Multiply counter_max hLen}) (decreases (counter_max - counter))

let rec mgf_sha256_loop mgfseed counter_max counter acc =
	if (counter < counter_max) then begin
		(**) assert(counter < pow2 (op_Multiply 8 4));
		let c = i2osp counter 4 in
		let mgfseed_c = append mgfseed c in
		(**) assert(length mgfseed_c = hLen + 4);
		(**) assert(length mgfseed_c < max_input_len_sha256);
		(**) assert(length acc = op_Multiply counter hLen);
		let acc = append acc (hash_sha256 mgfseed_c) in
		(**) assert(length acc = op_Multiply counter hLen + hLen);
		mgf_sha256_loop mgfseed counter_max (counter + 1) acc end
	else acc

val mgf_sha256:
	mgfseed:bytes{length mgfseed = hLen} ->
	maskLen:bignum{0 < maskLen /\ maskLen <= op_Multiply (pow2 32) hLen} ->
	Tot (mask:bytes{length mask = maskLen})

let mgf_sha256 mgfseed maskLen =
	(**) assert(maskLen - 1 < op_Multiply (pow2 32) hLen);
	(**) assert((maskLen - 1) / hLen < pow2 32);
	let counter_max = (maskLen - 1) / hLen + 1 in
	(**) assert(counter_max <= pow2 32);
	let acc = mgf_sha256_loop mgfseed counter_max 0 (createEmpty #UInt8.t) in
	slice acc 0 maskLen

val xorDB: b1:bytes -> b2:bytes{length b2 = length b1} -> Tot (res:bytes{length res = length b1})
let xorDB b1 b2 = Spec.Lib.map2 (fun x y -> U8.(x ^^ y)) b1 b2

val blit: #a:Type ->
	s1:seq a -> ind_s1:nat{ind_s1 <= length s1} ->
	s2:seq a -> ind_s2:nat{ind_s2 <= length s2} ->
	len:nat{ind_s1 + len <= length s1 /\ ind_s2 + len <= length s2} ->
	Tot (res:seq a{length res = length s2})
let rec blit #a s1 ind_s1 s2 ind_s2 len =
	if (len > 0) then begin
		let len = len - 1 in
		let s1_i = index s1 (ind_s1 + len) in
		let s2 = upd s2 (ind_s2 + len) s1_i in
		blit #a s1 ind_s1 s2 ind_s2 len end
	else s2

#reset-options "--z3rlimit 150"

val pss_encode:
	sLen:bignum ->
	modBits:pos{sLen + hLen + 2 <= get_length_em modBits} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	salt:bytes{length salt = sLen} -> Tot (em:bytes{length em = get_length_em modBits})

let pss_encode sLen modBits msg salt =
	let emLen = get_length_em modBits in
	let m1_size = 8 + hLen + sLen in
	let db_size = emLen - hLen - 1 in

	let m1 = create m1_size 0x00uy in
	let db = create db_size 0x00uy in
	let em = create emLen 0x00uy in

	let mHash = hash_sha256 msg in
	let m1 = blit mHash 0 m1 8 hLen in
	let m1 = blit salt 0 m1 (8 + hLen) sLen in
	let m1Hash = hash_sha256 m1 in admit();

	let ind_1 = emLen - sLen - hLen - 2 in
	let db = upd db ind_1 0x01uy in
	let db = blit salt 0 db (ind_1 + 1) sLen in
	assume(0 < db_size /\ db_size <= op_Multiply (pow2 32) hLen);
	let dbMask = mgf_sha256 m1Hash db_size in

	let maskedDB = xorDB db dbMask in
	let zeroL = op_Multiply 8 emLen - (modBits - 1) in
	assume(zeroL < 8);
	let maskedDB_0 = U8.((index maskedDB 0) &^ (0xffuy >>^ (bignum_to_uint32 zeroL))) in
	let maskedDB = upd maskedDB 0 maskedDB_0 in

	let em = blit maskedDB 0 em 0 db_size in
	let em = blit m1Hash 0 em db_size hLen in
	upd em (emLen - 1) 0xbcuy

#reset-options "--lax"

val pss_verify:
	sLen:bignum ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	em:bytes{length em = get_length_em modBits} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let pss_verify sLen modBits em msg =
	let emLen = get_length_em modBits in
	let m1_size = 8 + hLen + sLen in
	let pad_size = emLen - sLen - hLen - 1 in
	let db_size = emLen - hLen - 1 in

	let m1 = create m1_size 0x00uy in
	let pad2 = create pad_size 0x00uy in

	let mHash = hash_sha256 msg in
	if not (U8.(index em (emLen - 1) =^ 0xbcuy)) then false
	else begin
		let maskedDB, m1Hash_bc = split em db_size in
		let m1Hash, bc = split m1Hash_bc hLen in
		let zeroL = op_Multiply 8 emLen - (modBits - 1) in
		assume(zeroL < 8);
		let tmp = U8.((index maskedDB 0) &^ (0xffuy <<^ (bignum_to_uint32 (8 - zeroL)))) in
		if not (U8.(tmp =^ 0x00uy)) then false
		else begin
			assume(0 < db_size /\ db_size <= op_Multiply (pow2 32) hLen);
			let dbMask = mgf_sha256 m1Hash db_size in
			let db = xorDB maskedDB dbMask in
			let db_0 = U8.((index db 0) &^ (0xffuy >>^ (bignum_to_uint32 zeroL))) in
			let db = upd db 0 db_0 in
			let pad2 = upd pad2 (pad_size -1) 0x01uy in
			let pad, salt = split db pad_size in
			if not (pad = pad2) then false
			else begin
				(* first 8 elements should be 0x00 *)
				let m1 = blit mHash 0 m1 8 hLen in
				let m1 = blit salt 0 m1 (8 + hLen) sLen in
				let m1Hash' = hash_sha256 m1 in
				m1Hash = m1Hash'
			end
		end 
	end

val rsa_sign:
	sLen:bignum ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	skey:rsa_privkey ->
	salt:bytes{length salt = sLen} ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	Tot (sgnt:bytes{length sgnt = get_octets modBits})

let rsa_sign sLen modBits msg skey salt rBlind =
	let k = get_octets modBits in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in

	let em = pss_encode sLen modBits msg salt in
	let m = os2ip em in
	(* BLINDING *)
	let rBlind_inv, _ = extended_eucl rBlind n in
	let rBlind_e = mod_exp n rBlind e in
	let m1 = bignum_mul_mod m rBlind_e n in
	let s1 = mod_exp n m1 d in
	let s = bignum_mul_mod s1 rBlind_inv n in
	(**) assume(s < pow2 (op_Multiply 8 k));
	i2osp s k

val rsa_verify:
	sLen:bignum ->
	modBits:pos{sLen + hLen + 2 <= get_length_em modBits} ->
	sgnt:bytes{length sgnt = get_octets modBits} ->
	pkey:rsa_pubkey ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let rsa_verify sLen modBits sgnt pkey msg =
	let emLen = get_length_em modBits in
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in
	
	let s = os2ip sgnt in
	let s = bignum_mod s n in (* need to prove: s < n *)
	let m = mod_exp n s e in
	(**) assume(m < pow2 (op_Multiply 8 emLen));
	let em = i2osp m emLen in
	pss_verify sLen modBits em msg