module Spec.RSA

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.SHA2_256

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

(* PREREQUISITES *)

(* SEQUENCES *)

type seq 'a = s:Seq.seq 'a{length s < pow2 32}
type byte = UInt8.t
type bytes = seq byte
type lseq 'a n = s:seq 'a{length s = U32.v n}
type lbytes n = s:bytes{length s = U32.v n}


val create: #a:Type -> sz:U32.t -> v:a -> s:seq a{length s = U32.v sz}
let create #a s v = Seq.create #a (U32.v s) v

val upd: #a:Type -> s:seq a -> i:U32.t{U32.v i < length s} -> 
	 v:a -> s':seq a{length s' = length s}
let upd #a s i v = Seq.upd #a s (U32.v i) v

val index: #a:Type -> s:seq a -> i:U32.t{U32.v i < length s} -> a
let index #a s i = Seq.index #a s (U32.v i)

let op_String_Access = index
let op_String_Assignment = upd

val slice: #a:Type -> s:seq a -> i:U32.t -> j:U32.t{U32.v i <= U32.v j /\ U32.v j <= length s} -> t:seq a {length t = U32.v j - U32.v i}
let slice #a s i j = Seq.slice #a s (U32.v i) (U32.v j)

val seq_length: #a:Type -> s:seq a -> r:U32.t{U32.v r = length s}
let seq_length (#a:Type) (s:seq a) = U32.uint_to_t (length s)

val blit: #a:Type ->
	s1:seq a -> ind_s1:U32.t{U32.v ind_s1 <= length s1} ->
	s2:seq a -> ind_s2:U32.t{U32.v ind_s2 <= length s2} ->
	len:U32.t{U32.v ind_s1 + U32.v len <= length s1 /\ 
		  U32.v ind_s2 + U32.v len <= length s2} ->
	Tot (res:seq a{length res = length s2}) 
#reset-options "--z3rlimit 30"

let blit #a s1 ind_s1 s2 ind_s2 len =
    let t1 = slice s2 0ul ind_s2 in
    let t3 = slice s2 (ind_s2 +^ len) (seq_length s2)  in
    let f2 = slice s1 ind_s1 (ind_s1 +^ len)  in
    t1 @| f2 @| t3

val update_slice: #a:Type -> s:seq a -> i:U32.t -> l:U32.t{U32.v i + U32.v l <= length s} -> 
		  f: (s:lseq a l -> s:lseq a l) -> Tot (r:seq a{length r = length s})
let update_slice #a s i l f = 
    let s1 = slice s 0ul i in
    let s2 = slice s i (i +^ l) in
    let s3 = slice s (i +^ l) (seq_length s) in
    s1 @| (f s2) @| s3


val for_loop: min:U32.t -> max:U32.t{U32.v min <= U32.v max} -> f:('a -> i:U32.t{U32.v i < U32.v max} -> Tot 'a) -> x:'a -> Tot 'a
let for_loop min max f a = 
    Spec.Loops.repeat_range_spec (U32.v min) (U32.v max) (fun x i -> f x (U32.uint_to_t i)) a


(* SHA256 *)
let max_input_len_sha256 = pow2 61
unfold let hLen = 32ul
val hash_sha256:
	msg:bytes{length msg < max_input_len_sha256} -> 
	hash:lbytes hLen ->
	Tot (msgHash:lbytes hLen)
let hash_sha256 msg h = SHA2_256.hash msg

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

//let bignum_to_uint32 x = U32.uint_to_t (to_uint_t 32 x)
//let uint32_to_bignum x = U32.v x

(* RSA *)
type rsa_pubkey =
	| Mk_rsa_pubkey: n:pos -> e:elem n -> rsa_pubkey
	
type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey


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



(* BIGNUM LIB *)
val os2ip: b:bytes -> Tot bignum 
let os2ip b =
  let bLen = seq_length b in
  if (bLen = 0ul) 
  then 0 
  else
    let next (a:bignum) (i:U32.t{U32.v i < U32.v bLen - 1}): bignum = 
	       bignum_mul (bignum_add a (uint8_to_bignum b.[i])) 256 in
    let acc = for_loop 0ul (bLen -^ 1ul) next 0 in
    acc + U8.v (b.[bLen -^ 1ul])
    
val i2osp:
	n:bignum -> b:bytes{n < pow2 (8 * length b)} ->
	Tot (b':bytes{length b' = length b})
let i2osp n b =
	let bLen = seq_length b in
	if (bLen = 0ul)
	then b
	else
	let next (c:tuple2 bignum (lbytes bLen)) (i:U32.t{U32.v i < U32.v bLen}) : tuple2 bignum (lbytes bLen) =
	    let (n,b) = c in
	    let b' = b.[bLen -^ i -^ 1ul] <- bignum_to_uint8 (bignum_mod n 256) in
	    let n' = bignum_div n 256 in
	    (n',b') in
  
        let (n',b') = for_loop 0ul bLen next (n,b) in
	b'

val mgf_sha256_loop:
	mgfseed:bytes{length mgfseed = (U32.v hLen) + 4} ->
        counter_max:UInt32.t ->
	acc:bytes{length acc = U32.v counter_max * U32.v hLen /\ length acc < pow2 32} ->
	Tot (res:bytes{length res = length acc})

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

val store32_be: U32.t -> lbytes 4ul -> lbytes 4ul
let store32_be (i:U32.t) (b:lbytes 4ul) : lbytes 4ul = FStar.Endianness.uint32_be 4ul i

let mgf_sha256_loop mgfseed counter_max acc =
    let mHash = create 32ul 0uy in
    let accLen = seq_length acc in
    let acc: lbytes accLen = acc in
    let next (acc:lbytes accLen) (i:U32.t{U32.v i < U32.v counter_max}) : lbytes accLen =
    	let mgfseed = update_slice mgfseed hLen 4ul (store32_be i) in
		let mHash = hash_sha256 mgfseed mHash in
		blit mHash 0ul acc (hLen *^ i) hLen in
    for_loop #(lbytes accLen) 0ul counter_max next acc


val blocks: x:U32.t{U32.v x > 0} -> m:U32.t{U32.v m > 0} -> r:U32.t{U32.v r > 0}
let blocks (x:U32.t{U32.v x > 0}) (m:U32.t{U32.v m > 0}) = (x -^ 1ul) /^ m +^ 1ul

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

val xor_bytes: b1:bytes -> b2:bytes{length b2 = length b1} -> Tot (res:bytes{length res = length b1})
let xor_bytes b1 b2 = Spec.Lib.map2 (fun x y -> U8.(x ^^ y)) b1 b2


val pss_encode_:
	msBits:U32.t{U32.v msBits < 8} ->
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	em:bytes{length em - length salt - U32.v hLen - 2 >= 0} ->
	Tot (em':bytes{length em = length em'})

let pss_encode_ msBits salt msg em =
	let mHash = create 32ul 0uy in
	let mHash = hash_sha256 msg mHash in

	let sLen = seq_length salt in
	let emLen = seq_length em in

	let m1_size = 8ul +^ hLen +^ sLen in
	let m1 = create m1_size 0x00uy in
	let m1 = blit mHash 0ul m1 8ul hLen in
	let m1 = blit salt 0ul m1 (8ul +^ hLen) sLen in
	let m1Hash = create 36ul 0uy in
	let m1Hash = update_slice m1Hash 0ul 32ul (hash_sha256 m1) in
	
	let db_size = emLen -^ hLen -^ 1ul in
	let db = create db_size 0x00uy in
	let last_before_salt = db_size -^ sLen -^ 1ul in
	let db = db.[last_before_salt] <- 0x01uy in
	let db = blit salt 0ul db (last_before_salt +^ 1ul) sLen in

    let dbMask = create db_size 0uy in
	let dbMask = mgf_sha256 m1Hash db_size dbMask in
	let maskedDB = xor_bytes db dbMask in
	let maskedDB = 
		if msBits >^ 0ul
		then maskedDB.[0ul] <- U8.(maskedDB.[0ul] &^ (0xffuy >>^ U32.(8ul -^ msBits)))
		else maskedDB in

	let em = blit maskedDB 0ul em 0ul db_size in
	let em = blit m1Hash 0ul em db_size hLen in
    upd em (emLen -^ 1ul) 0xbcuy

val pss_encode:
	msBits:U32.t{U32.v msBits < 8} ->
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32} -> 
	msg:bytes{length msg < max_input_len_sha256} ->
	em:bytes{length em > 0} ->
	Tot (res:bytes{length res = length em})

let pss_encode msBits salt msg em =
	let emLen = seq_length em in
	if msBits =^ 0ul
	then update_slice em 1ul (emLen -^ 1ul) (pss_encode_ msBits salt msg)
	else pss_encode_ msBits salt msg em

val pss_verify_:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	msBits:U32.t{U32.v msBits < 8} ->
	em:bytes{length em - U32.v sLen - U32.v hLen - 2 >= 0} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let pss_verify_ sLen msBits em msg =
	let emLen = seq_length em in
	let mHash = create 32ul 0uy in
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
	if not (pad = pad2) then false
	else begin
		(* first 8 elements should be 0x00 *)
		let m1 = blit mHash 0ul m1 8ul hLen in
		let m1 = blit salt 0ul m1 (8ul +^ hLen) sLen in
		let m1Hash' = create 32ul 0uy in
		let m1Hash' = hash_sha256 m1 m1Hash' in
		m1Hash0 = m1Hash'
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
	modBits:U32.t{U32.v modBits > 0} ->
	skey:rsa_privkey ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	salt:bytes{length salt + U32.v hLen + 8 < pow2 32} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	Tot (sgnt:bytes{length sgnt = U32.v (blocks modBits 8ul)})

let rsa_sign modBits skey rBlind salt msg =
	let k = blocks modBits 8ul in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in

	let msBits = (modBits -^ 1ul) %^ 8ul in
	let em = create k 0x00uy in
	(**) assume(U32.v msBits < 8);
	let em = pss_encode msBits salt msg em in
	let m = os2ip em in
	(* BLINDING *)
	let rBlind_inv, _ = extended_eucl rBlind n in
	let rBlind_e = mod_exp n rBlind e in
	let m1 = bignum_mul_mod m rBlind_e n in
	let s1 = mod_exp n m1 d in
	let s = bignum_mul_mod s1 rBlind_inv n in
	let sgnt = create k 0x00uy in
	(**) assume(s < pow2 (8 * U32.v k));
	i2osp s sgnt

val rsa_verify:
	modBits:U32.t{U32.v modBits > 0} ->
	pkey:rsa_pubkey ->
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	sgnt:bytes{length sgnt = U32.v (blocks modBits 8ul)} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let rsa_verify modBits pkey sLen sgnt msg =
	let k = blocks modBits 8ul in
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in
	
	let s = os2ip sgnt in
	let s = bignum_mod s n in (* need to prove: s < n *)
	let m = mod_exp n s e in
	(**) assume(m < pow2 (8 * U32.v k));
	let em = create k 0x00uy in
	let em = i2osp m em in
	let msBits = (modBits -^ 1ul) %^ 8ul in
	(**) assume(U32.v msBits < 8);
	pss_verify sLen msBits em msg