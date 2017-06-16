module Spec.RSA

open FStar.Seq
open FStar.UInt8
open FStar.UInt32
open FStar.Mul
open FStar.UInt
open Spec.SHA256

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

(* a*x + b*y = gcd(a,b) *)
val extended_eucl: a:nat -> b:nat -> Tot (tuple2 int int) (decreases b)
let rec extended_eucl a b =
	if b = 0 then (1, 0)
	else
		match (extended_eucl b (a % b)) with
		| (x, y) -> (y, x - (op_Multiply (a/b) y))

val mod_mult_mont: n:pos -> r:pos -> n':int -> a_r: elem n -> b_r: elem n -> Tot (res:elem n)
let mod_mult_mont n r n' a_r b_r =
	let t = op_Multiply a_r b_r in
	let m = (op_Multiply t n') % r in
	let u = (t + op_Multiply m n) / r in
	(* if u >= n then u - n else u *)
	u % n

val pow_mont: modBits:nat -> n:pos -> r:pos -> n':int -> a_r: elem n -> b: elem n -> acc_r: elem n -> Tot (res:elem n)
let rec pow_mont modBits n r n' a_r b acc_r =
	if modBits > 0 then 
		let counter = modBits - 1 in 
		let b_i = (b / pow2 counter) % 2 in
		let acc_r = mod_mult_mont n r n' acc_r acc_r in
		let acc_r = if b_i = 1 then mod_mult_mont n r n' a_r acc_r else acc_r in
		pow_mont counter n r n' a_r b acc_r
	else  acc_r

val mod_exp_mont: modBits:pos -> n:pos -> a:elem n -> b:elem n -> Tot (res:elem n)
let mod_exp_mont modBits n a b =
	let r = pow2 modBits in
	let (r', n') = extended_eucl r n in
	let a_r = (op_Multiply a r) % n in
	let acc_r = r % n in
	let n' = op_Multiply n' (-1) in
	let acc_r = pow_mont modBits n r n' a_r b acc_r in
	(* let elem_n_1 = 1 % n *)
	mod_mult_mont n r n' acc_r 1

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
let hash_sha256 msg = SHA256.hash msg

(* assume val random_bytes: len: pos -> Tot (res:bytes{length res = len}) *)

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
	let s = mod_exp_mont modBits n m d in
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
	let m = mod_exp_mont modBits n s e in
	let emLen = get_length_em modBits in
	let em = nat_to_text m emLen in
	pss_verify modBits em msg

(* RSASSA-PSS Signature Example 1.2 *)
(* http://www.das-labor.org/svn/microcontroller-2/arm-crypto-lib/testvectors/rsa-pkcs-1v2-1-vec/pss-vect.txt *)

let test() =
	let msg = createL [
	 	0x85uy; 0x13uy; 0x84uy; 0xcduy; 0xfeuy; 0x81uy; 0x9cuy; 0x22uy; 0xeduy; 0x6cuy; 0x4cuy; 0xcbuy; 0x30uy; 0xdauy; 0xebuy; 0x5cuy; 
		0xf0uy; 0x59uy; 0xbcuy; 0x8euy; 0x11uy; 0x66uy; 0xb7uy; 0xe3uy; 0x53uy; 0x0cuy; 0x4cuy; 0x23uy; 0x3euy; 0x2buy; 0x5fuy; 0x8fuy;
	 	0x71uy; 0xa1uy; 0xccuy; 0xa5uy; 0x82uy; 0xd4uy; 0x3euy; 0xccuy; 0x72uy; 0xb1uy; 0xbcuy; 0xa1uy; 0x6duy; 0xfcuy; 0x70uy; 0x13uy; 
		0x22uy; 0x6buy; 0x9euy] in
	let salt = createL [
	    0xefuy; 0x28uy; 0x69uy; 0xfauy; 0x40uy; 0xc3uy; 0x46uy; 0xcbuy; 0x18uy; 0x3duy; 0xabuy; 0x3duy; 0x7buy; 0xffuy; 0xc9uy; 0x8fuy;
		0xd5uy; 0x6duy; 0xf4uy; 0x2duy] in
	let n = createL [
		0xa5uy; 0x6euy; 0x4auy; 0x0euy; 0x70uy; 0x10uy; 0x17uy; 0x58uy; 0x9auy; 0x51uy; 0x87uy; 0xdcuy; 0x7euy; 0xa8uy; 0x41uy; 0xd1uy;
		0x56uy; 0xf2uy; 0xecuy; 0x0euy; 0x36uy; 0xaduy; 0x52uy; 0xa4uy; 0x4duy; 0xfeuy; 0xb1uy; 0xe6uy; 0x1fuy; 0x7auy; 0xd9uy; 0x91uy;
		0xd8uy; 0xc5uy; 0x10uy; 0x56uy; 0xffuy; 0xeduy; 0xb1uy; 0x62uy; 0xb4uy; 0xc0uy; 0xf2uy; 0x83uy; 0xa1uy; 0x2auy; 0x88uy; 0xa3uy;
		0x94uy; 0xdfuy; 0xf5uy; 0x26uy; 0xabuy; 0x72uy; 0x91uy; 0xcbuy; 0xb3uy; 0x07uy; 0xceuy; 0xabuy; 0xfcuy; 0xe0uy; 0xb1uy; 0xdfuy;
		0xd5uy; 0xcduy; 0x95uy; 0x08uy; 0x09uy; 0x6duy; 0x5buy; 0x2buy; 0x8buy; 0x6duy; 0xf5uy; 0xd6uy; 0x71uy; 0xefuy; 0x63uy; 0x77uy;
		0xc0uy; 0x92uy; 0x1cuy; 0xb2uy; 0x3cuy; 0x27uy; 0x0auy; 0x70uy; 0xe2uy; 0x59uy; 0x8euy; 0x6fuy; 0xf8uy; 0x9duy; 0x19uy; 0xf1uy;
		0x05uy; 0xacuy; 0xc2uy; 0xd3uy; 0xf0uy; 0xcbuy; 0x35uy; 0xf2uy; 0x92uy; 0x80uy; 0xe1uy; 0x38uy; 0x6buy; 0x6fuy; 0x64uy; 0xc4uy;
		0xefuy; 0x22uy; 0xe1uy; 0xe1uy; 0xf2uy; 0x0duy; 0x0cuy; 0xe8uy; 0xcfuy; 0xfbuy; 0x22uy; 0x49uy; 0xbduy; 0x9auy; 0x21uy; 0x37uy] in
	let e = createL [0x01uy; 0x00uy; 0x01uy] in
	let d = createL [
		0x33uy; 0xa5uy; 0x04uy; 0x2auy; 0x90uy; 0xb2uy; 0x7duy; 0x4fuy; 0x54uy; 0x51uy; 0xcauy; 0x9buy; 0xbbuy; 0xd0uy; 0xb4uy; 0x47uy; 
		0x71uy; 0xa1uy; 0x01uy; 0xafuy; 0x88uy; 0x43uy; 0x40uy; 0xaeuy; 0xf9uy; 0x88uy; 0x5fuy; 0x2auy; 0x4buy; 0xbeuy; 0x92uy; 0xe8uy; 
		0x94uy; 0xa7uy; 0x24uy; 0xacuy; 0x3cuy; 0x56uy; 0x8cuy; 0x8fuy; 0x97uy; 0x85uy; 0x3auy; 0xd0uy; 0x7cuy; 0x02uy; 0x66uy; 0xc8uy; 
		0xc6uy; 0xa3uy; 0xcauy; 0x09uy; 0x29uy; 0xf1uy; 0xe8uy; 0xf1uy; 0x12uy; 0x31uy; 0x88uy; 0x44uy; 0x29uy; 0xfcuy; 0x4duy; 0x9auy; 
		0xe5uy; 0x5fuy; 0xeeuy; 0x89uy; 0x6auy; 0x10uy; 0xceuy; 0x70uy; 0x7cuy; 0x3euy; 0xd7uy; 0xe7uy; 0x34uy; 0xe4uy; 0x47uy; 0x27uy; 
		0xa3uy; 0x95uy; 0x74uy; 0x50uy; 0x1auy; 0x53uy; 0x26uy; 0x83uy; 0x10uy; 0x9cuy; 0x2auy; 0xbauy; 0xcauy; 0xbauy; 0x28uy; 0x3cuy; 
		0x31uy; 0xb4uy; 0xbduy; 0x2fuy; 0x53uy; 0xc3uy; 0xeeuy; 0x37uy; 0xe3uy; 0x52uy; 0xceuy; 0xe3uy; 0x4fuy; 0x9euy; 0x50uy; 0x3buy; 
		0xd8uy; 0x0cuy; 0x06uy; 0x22uy; 0xaduy; 0x79uy; 0xc6uy; 0xdcuy; 0xeeuy; 0x88uy; 0x35uy; 0x47uy; 0xc6uy; 0xa3uy; 0xb3uy; 0x25uy ] in	
	let n = text_to_nat n in
	let e = text_to_nat e in
	let d = text_to_nat d in
	let pkey = Mk_rsa_pubkey n e in
	let skey = Mk_rsa_privkey pkey d in
	let sgnt = rsa_sign 1024 msg skey salt in
	rsa_verify 1024 sgnt pkey msg