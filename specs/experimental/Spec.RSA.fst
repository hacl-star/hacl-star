module Spec.RSA

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.SHA2_256

module U8 = FStar.UInt8
module U32 = FStar.UInt32

let max_input_len_sha256 = pow2 61
let hLen = 32
let sLen = 20

type byte = UInt8.t
type bytes = seq byte

type elem (n:pos) = e:int{e >= 0 /\ e < n}

type rsa_pubkey = 
	| Mk_rsa_pubkey: n:pos -> e:elem n -> rsa_pubkey

val get_n: x:rsa_pubkey -> Tot pos
let get_n x = 
	match x with 
	| Mk_rsa_pubkey n e -> n
	
val get_e: x:rsa_pubkey -> Tot (e:elem (get_n x))
let get_e x =
	match x with
	| Mk_rsa_pubkey n e -> e
	
type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:elem (get_n pkey) -> rsa_privkey
	
val get_pkey: x:rsa_privkey -> Tot rsa_pubkey
let get_pkey x =
	match x with
	| Mk_rsa_privkey pkey d -> pkey

val get_d: x:rsa_privkey -> Tot (e:elem (get_n (get_pkey x))) 	
let get_d x =
	match x with
	| Mk_rsa_privkey pkey d -> d

val nat_to_uint8: x:nat -> Tot UInt8.t
let nat_to_uint8 x = U8.uint_to_t (to_uint_t 8 x)

val nat_to_uint32: x:nat -> Tot UInt32.t
let nat_to_uint32 x = U32.uint_to_t (to_uint_t 32 x)

val mod_exp_loop: n:pos -> a:nat -> b:nat -> acc:elem n -> Tot (res:elem n)
let rec mod_exp_loop n a b acc = 
	match b with
	| 0 -> acc
	| 1 -> (op_Multiply a acc) % n
	| e -> 
		let a2 = (op_Multiply a a) % n in
		if (e % 2 = 0) then mod_exp_loop n a2 (b/2) acc
		else 
			let acc = (op_Multiply a acc) % n in 
			mod_exp_loop n a2 ((b - 1)/2) acc
		 
val mod_exp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n)
let mod_exp n a b = mod_exp_loop n a b 1

val text_to_nat: b:bytes -> Tot nat (decreases (Seq.length b))
let rec text_to_nat b =
	let bLen = Seq.length b in
	if bLen = 0 then 0
	else op_Multiply (U8.v (head b)) (pow2 (op_Multiply 8 (bLen - 1))) + (text_to_nat (tail b))

(* if (n >= pow2 (op_Multiply 8 bLen) ) then failwith "integer too large" *)
val nat_to_text: n:nat -> bLen:nat -> Tot (b:bytes{length b = bLen}) (decreases bLen)
let rec nat_to_text n bLen =
	if bLen = 0 then createEmpty #UInt8.t
	else
		let len = bLen - 1 in
		let t = pow2 (op_Multiply 8 len) in
		let x = nat_to_uint8 (n / t) in
		let n = n % t in
		append (create 1 x) (nat_to_text n len)

val get_octets: modBits: pos -> Tot nat
let get_octets modBits = (modBits + 7)/8 
(* or better: (modBits-1)/8 + 1 *)

val get_length_em: modBits:pos -> Tot nat
let get_length_em modBits =
	 let k = get_octets modBits in  
	 if ((modBits - 1) % 8 = 0)
	 then k - 1 else k

val hash_sha256: msg:bytes{length msg < max_input_len_sha256} -> Tot (msgHash:bytes{length msgHash = hLen})
let hash_sha256 msg = SHA2_256.hash msg

val mgf: mgfseed:bytes -> len:nat -> counter:nat -> 
acc: bytes {length acc = op_Multiply counter hLen} -> 
Tot (res:bytes{length res = len}) (decreases (len - op_Multiply counter hLen))
let rec mgf mgfseed len counter acc =
	(* if len > op_Multiply (pow2 32) hLen then failwith "mask too long" *)
	let c = nat_to_text counter 4 in
	let tmp = append mgfseed c in
	let acc = append acc (hash_sha256 tmp) in
	let counter = counter + 1 in
	if (op_Multiply counter hLen < len) then 
		mgf mgfseed len counter acc	
	else
		let res, tmp = split acc len in
		res

val xorDB: 
b1:bytes ->
b2:bytes{length b2 = length b1} -> 
len:nat{len <= length b1} -> Tot (res:bytes{length res = length b1}) (decreases len)
let rec xorDB b1 b2 len = 
	if (len > 0) then
		let len = len - 1 in 
		let tmp = U8.((index b1 len) ^^ (index b2 len)) in
		let b1 = upd b1 len tmp in 
		xorDB b1 b2 len
	else b1

val pss_encode:
modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
msg:bytes{length msg < max_input_len_sha256} ->
salt:bytes{length salt = sLen} -> Tot (em:bytes{length em = get_length_em modBits})
let pss_encode modBits msg salt =
	let mHash = hash_sha256 msg in
	let emBits = modBits - 1 in 
	let emLen = get_length_em modBits in
	let m1 = append (create 8 0x00uy) (append mHash salt) in 
	let m1Hash = hash_sha256 m1 in
	let ps = create (emLen - sLen - hLen - 2) 0x00uy in
	let db = append ps (append (create 1 0x01uy) salt) in
	let dbMask = mgf m1Hash (emLen - hLen - 1) 0 (createEmpty #UInt8.t) in 
	let maskedDB = xorDB db dbMask (emLen - hLen - 1) in
	let zeroL = nat_to_uint32 (op_Multiply 8 emLen - emBits) in
	let tmp = U8.((index maskedDB 0) &^ (0xffuy >>^ zeroL)) in
	let maskedDB = upd maskedDB 0 tmp in
	append maskedDB (append m1Hash (create 1 0xbcuy))

val pss_verify: 
modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
em:bytes{length em = get_length_em modBits} ->
msg:bytes{length msg < max_input_len_sha256} -> Tot bool
let pss_verify modBits em msg = 
	let mHash = hash_sha256 msg in
	let emLen = get_length_em modBits in
	if not (U8.(index em (emLen - 1) =^ 0xbcuy)) then false else
	let maskedDB, rest = split em (emLen - hLen - 1) in
	let m1Hash, lelem = split rest hLen in
	let zeroL = op_Multiply 8 emLen - (modBits - 1) in
	let tmp = U8.((index maskedDB 0) &^ (0xffuy <<^ (nat_to_uint32 (8 - zeroL)))) in 
	if not (U8.(tmp =^ 0x00uy)) then false else
	let dbMask = mgf m1Hash (emLen - hLen - 1) 0 (createEmpty #UInt8.t) in
	let db = xorDB maskedDB dbMask (emLen - hLen - 1) in
	let tmp = U8.((index db 0) &^ (0xffuy >>^ (nat_to_uint32 zeroL))) in
	let db = upd db 0 tmp in
	let pad2 = create (emLen - sLen - hLen - 2) 0x00uy in
	let pad2 = append pad2 (create 1 0x01uy) in
	let pad, salt = split db (emLen - sLen - hLen - 1) in
	if not (pad = pad2) then false else
	let pad1 = create 8 0x00uy in
	let m1 = append pad1 (append mHash salt) in
	let m1Hash' = hash_sha256 m1 in
	m1Hash = m1Hash'

(* msg -> em *)
(* |n| = modBits = k;
   |em| = get_length_em modBits = k or k-1;
   |sgnt| = get_octets modBits = k *)
val rsa_sign:
modBits: pos{get_length_em modBits >= sLen + hLen + 2} ->
msg:bytes{length msg < max_input_len_sha256} ->
skey:rsa_privkey ->
salt:bytes{length salt = sLen} -> Tot (sgnt:bytes{length sgnt = get_octets modBits})
let rsa_sign modBits msg skey salt =
	let k = get_octets modBits in 
	let d = get_d skey in
	let n = get_n (get_pkey skey) in

	let em = pss_encode modBits msg salt in
	let m = text_to_nat em in
	let m = m % n in
	let s = mod_exp n m d in
	nat_to_text s k

val rsa_verify:
modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
sgnt:bytes{length sgnt = get_octets modBits} -> 
pkey:rsa_pubkey ->
msg:bytes{length msg < max_input_len_sha256} -> Tot bool
let rsa_verify modBits sgnt pkey msg =
	let e = get_e pkey in
	let n = get_n pkey in
	
	let s = text_to_nat sgnt in
	let s = s % n in
	let m = mod_exp n s e in
	let emLen = get_length_em modBits in
	let em = nat_to_text m emLen in
	pss_verify modBits em msg