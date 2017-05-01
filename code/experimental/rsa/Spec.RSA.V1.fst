module Spec.RSA.V1

open FStar.Seq
open FStar.UInt8
open FStar.Mul
open FStar.UInt

module U8 = FStar.UInt8

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
	
type byte = UInt8.t
type bytes = seq byte

val pow: a:nat -> n:nat -> Tot nat
let rec pow a n =
	match n with
	| 0 -> 1
	| _ -> 
		let b = pow a (n/2) in
		b * b * (if n % 2 = 0 then 1 else a)

val fexp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n) 
let fexp n a b = (pow a b) % n

val text_to_nat: b:bytes -> Tot nat (decreases (Seq.length b))
let rec text_to_nat b =
	let bLen = Seq.length b in
	if bLen = 0 then 0
	else U8.v (head b) * (pow2 8 * (bLen - 1)) + (text_to_nat (tail b))

assume val nat_to_uint8: x:nat -> Tot UInt8.t
 
val nat_to_text: n:nat -> bLen:nat -> Tot (b:bytes{length b = bLen}) (decreases bLen)
let rec nat_to_text n bLen =
	(* if (n >= pow 256 bLen) then failwith "integer too large" *)
	if bLen = 0 then createEmpty
	else
		let len = bLen - 1 in
		let t = pow2 (8 * len) in
		let x = nat_to_uint8 (n / t) in
		let n = n % t in
		append (create 1 x) (nat_to_text n len)

(* msg -> em *)
(* |n| = k; |em| = k or |em| = k - 1; |sgnt| = k *)
val rsa_sign: k:pos -> msg:bytes{length msg = k \/ length msg = k - 1} -> skey:rsa_privkey -> Tot (sgnt:bytes{length sgnt = k})
let rsa_sign k msg skey =
	let d = get_d skey in
	let n = get_n (get_pkey skey) in
	let m = text_to_nat msg in
	let m = m % n in
	let s = fexp n m d in
	nat_to_text s k

val rsa_verify: k:pos -> sgnt:bytes{length sgnt = k} -> pkey:rsa_pubkey -> msg:bytes{length msg = k \/ length msg = k - 1} -> Tot bool	
let rsa_verify k sgnt pkey msg =
	let e = get_e pkey in
	let n = get_n pkey in
	let s = text_to_nat sgnt in
	let s = s % n in
	let m = fexp n s e in
	let k = length msg in
	Seq.eq msg (nat_to_text m k)