module Spec.RSA

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
	
val pow: a:nat -> n:nat -> Tot nat
let rec pow a n =
	match n with
	| 0 -> 1
	| _ -> 
		let b = pow a (n/2) in
		b * b * (if n % 2 = 0 then 1 else a)

val fexp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n) 
let fexp n a b = (pow a b) % n

val rsa_sign: skey:rsa_privkey -> msg:nat{msg < get_n (get_pkey skey)}  -> Tot (sgnt:nat{sgnt < get_n (get_pkey skey)})
let rsa_sign skey msg =
	let d = get_d skey in
	let n = get_n (get_pkey skey) in
	fexp n msg d

val rsa_verify: pkey:rsa_pubkey -> sgnt:nat{sgnt < get_n pkey} -> msg:nat{msg < get_n pkey} -> Tot bool	
let rsa_verify pkey sgnt msg =
	let e = get_e pkey in
	let n = get_n pkey in
	let m = fexp n sgnt e in
	m = msg
	
let test() = 
	let n = 3233 in
	let e = 17 in
	let d = 413 in
	let m = 65 in 
	let sgnt = rsa_sign (Mk_rsa_privkey (Mk_rsa_pubkey n e) d) m in
	rsa_verify (Mk_rsa_pubkey n e) sgnt m 