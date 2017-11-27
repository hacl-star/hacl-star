module Spec.P256

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let prime = pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 
let cardinality = 115792089210356248762697446949407573529996955224135760342422259061068512044369 

type elem : Type0 = e:int{e >= 0 /\ e < prime}

let fadd e1 e2 = (e1 + e2) % prime
let fsub e1 e2 = (e1 - e2) % prime
let fmul e1 e2 = (e1 * e2) % prime

let rec ( ** ) (e:elem) (n:pos) : Tot elem (decreases n) =
  if n = 1 then e
  else
    if n % 2 = 0 then op_Star_Star (e `fmul` e) (n / 2)
    else e `fmul` (op_Star_Star (e `fmul` e) ((n-1)/2))

let modp_inv (x:elem) : Tot elem =
  (x ** (prime - 2)) % prime

type scalar = lbytes 32  
type serialized_point = lbytes 33
type jacobian = |Jacobian: x: elem -> y: elem -> z: elem -> jacobian
type affine = |Affine: x1: elem -> y1: elem -> affine

val toAffineJ: p: jacobian -> Tot (jacobian)
let toAffineJ p = 
		let z2 = p.z **2 in 
		let z2i = modp_inv z2 in 
		let z3 = p.z**3 in 
		let z3i = modp_inv z3 in 
		Jacobian (fmul p.x z2i) (fmul p.y z3i) (1)

val toAffine: p: jacobian -> Tot (affine)
let toAffine p = 
	let p = toAffineJ p in 
	Affine (p.x) (p.y)		

(*)
prime = 115792089210356248762697446949407573530086143415290314195533631308867097853951
a = -3
b = 41058363725152142129326129780047268409114441015993725554835256314039467401291

x = 48439561293906451759052585252797914202762949526041747995844080717082404635286 
y = 36134250956749795798585127919587881956611106672985015071877198253568414405109
z = 1

z2 = z^2
z2i = inverse_mod(z2, prime)
z3 = z^3
z3i = inverse_mod(z3, prime)

x_ = (x * z2i) % prime
y_ = (y*z3i) % prime

y__ = (y_ % 2)*2^256
num = x_ + y__


sign = (num // (2^256)) % 2

x = num % 2^256

x3 = (x^3) % prime
ax = a * x 
z = (x3 + ax + b) % prime

p = (prime +1) // 4

z1 = z**p % prime
z2 = prime -z1

*)
val point_compress: (p: jacobian) -> Tot (serialized_point)
let point_compress p = 
	let z2 = p.z **2 in
	let z2i = modp_inv z2 in 
	let z3 = p.z**3 in 
	let z3i = modp_inv z3 in 
	let p = pow2 256 * ((fmul p.y z3i) % 2) + (fmul p.x z2i) in
	nat_to_bytes_le 33 p

let b = 41058363725152142129326129780047268409114441015993725554835256314039467401291
let a = prime - 3


val recover_y: x:elem ->  sign:bool -> Tot (option elem)
let recover_y x sign = 
	let x3 = x**3 in 
	let ax = fmul a x in 
	let z = fadd (fadd x3 ax) b in 
	let p = (prime +1) / 4 in 
	let z1 = z ** p in 
	if (sign) then 
		Some (prime - z1) 
	else Some z1	

let point_decompress (s:lbytes 33) : Tot (option jacobian) =
  let x = nat_from_bytes_le s in
  let sign = (x / pow2 256) % 2 = 1 in
  let x = x % (pow2 256) in
  let y = recover_y x sign in
  match y with
  | Some y ->  Some (Jacobian (x%prime) (y % prime) 1)
  | _ -> None

let point_double p = 
	let x1 = p.x in 
	let y1 = p.y in 
	let z1 = p.z in 
	let delta = z1**2 in 
	let gamma = y1**2 in 
	let beta = x1 `fmul` gamma in 
	let alpha = 3 `fmul` (x1 `fsub` delta) `fmul` (x1 `fadd` delta) in 
	let x3 = (alpha **2) `fsub` (8 `fmul` beta) in 
	let z3 = ((y1 `fadd` z1) **2) `fsub` gamma `fsub` delta in 
	let y3 = alpha `fmul` (4 `fmul` beta `fsub` x3) `fsub` (8 `fmul` (gamma**2)) in
	Jacobian x3 y3 z3 
(*)
val point_add1: p: jacobian -> q:jacobian -> Tot jacobian 

let point_add1 p q = 
	if isPointOnInfinity p && isPointOnInfinity q then p
	else if isPointOnInfinity p then q 
	else if isPointOnInfinity q then p 
	else if (p.x = q.x && (p.y <> q.y || (p.y = 0 && q.y = 0)))
	 	then Jacobian 1 1 0
	else if (p.y = q.x && (p.y = q.y)) then point_double p 
	else	
		(let x1 = p.x in 
	let y1 = p.y in 
	let z1 = p.z in 
	let x2 = q.x in 
	let y2 = q.y in 
	let z2 = q.z in 
	let z1z1 = z1**2 in 
	let z2z2 = z2**2 in 
	let u1 = x1 `fmul` z2z2	in 
	let u2 = x2 `fmul` z1z1 in 
	let s1 = y1 `fmul` z2 `fmul` z2z2 in 
	let s2 = y2 `fmul` z1 `fmul` z1z1 in 	
	let h = u2 `fsub` u1 in 
	let i = (2 `fmul` h)**2 in 
	let j = h `fmul` i in 
	let r = 2 `fmul` (s2 `fsub` s1) in 
	let v = u1 `fmul` i in 
	let x3 = (r**2) `fsub` j `fsub` (2 `fmul` v) in 
	let y3 = r `fmul` (v `fsub` x3) `fsub` (2 `fmul` s1 `fmul` j) in 
	let z3_part = (fadd z1 z2) **2 in 
		let z3 = (z3_part `fsub` z1z1 `fsub` z2z2) `fmul` h in
		Jacobian x3 y3 z3
	)
*)


val point_add : p: jacobian -> q: jacobian ->Tot jacobian

let point_add p q = 
	let x1 = p.x in 
	let y1 = p.y in 
	let z1 = p.z in 
	let x2 = q.x in 
	let y2 = q.y in 
	let z2 = q.z in 
	let z1z1 = z1**2 in 
	let z2z2 = z2**2 in 
	let u1 = x1 `fmul` z2z2	in 
	let u2 = x2 `fmul` z1z1 in 
	let s1 = y1 `fmul` z2 `fmul` z2z2 in 
	let s2 = y2 `fmul` z1 `fmul` z1z1 in 
		if (u1 = u2) then 
			(
				if (s1 = s2) then
					point_double p
				else 
					Jacobian 1 1 0	
			) 
		else
		(	
	let h = u2 `fsub` u1 in 
	let i = (2 `fmul` h)**2 in 
	let j = h `fmul` i in 
	let r = 2 `fmul` (s2 `fsub` s1) in 
	let v = u1 `fmul` i in 
	let x3 = (r**2) `fsub` j `fsub` (2 `fmul` v) in 
	let y3 = r `fmul` (v `fsub` x3) `fsub` (2 `fmul` s1 `fmul` j) in 
	let z3_part = (fadd z1 z2) **2 in 
	let z3 = (z3_part `fsub` z1z1 `fsub` z2z2) `fmul` h in
	Jacobian x3 y3 z3
	) 	

let ith_bit (k:scalar) (i:nat{i < 256}) =
  let q = i / 8 in let r = u32 (i % 8) in
  (k.[q] >>. r) &. u8 1

let basePoint = 
	Jacobian (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296)
	 (0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5) 
	 (0x1)     

let doubleBasePoint = 
	Jacobian(0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978)
	(0x7775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1)
	(0x1)

val montgomery_ladder_ : r0: jacobian ->  r1: jacobian -> k: scalar -> counter: int{counter < 256} -> jacobian

let rec montgomery_ladder_ r0 r1 k counter = 
	if counter < 0 then r0
	else (
		let (r0, r1) = 
				if ith_bit k counter = 1 then 
					(point_add r0 r1, point_double r1)
				else 
					(point_double r0, point_add r0 r1)
		 
		in montgomery_ladder_ r0 r1 k (counter - 1)
	)

(*The smallest scalar kk for which [k]P=∞[k]P=∞ is called the order of PP. *)
val key_s: k: scalar -> Tot (r: option nat {Some? r ==>	Some?.v r < 256})
let key_s k = 
	let rec key_s_ins counter k  = 
		if counter < 0 then None
	else (
		if ith_bit k counter = 1 then Some counter 
			else key_s_ins (counter -1) k
		) 
	in key_s_ins 255 k


val montgomery_ladder: point: jacobian -> k: scalar -> Tot jacobian
let montgomery_ladder point k = 
	let pointD = point_double point in 
	if Some?(key_s k) then 
		montgomery_ladder_  point pointD k (Some?.v (key_s k))
	else
		basePoint	
		
let pointAtInf = Jacobian (0x0) (0x1) (0x0)

val montgomery_ladder2: point: jacobian -> k: scalar -> Tot jacobian
let montgomery_ladder2 point k = 
	let r0 = pointAtInf in 
	let r1 = point in 
	montgomery_ladder_ r0 r1 k 255


let sk1 = [0x13uy; 0xeuy;  0xeduy; 0x5euy; 0xb9uy; 0xbbuy; 0x8euy; 0x1uy;
           0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
           0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
           0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy
]

let p1 = 
	Jacobian (23324703808854041287334488211846703542455270615548541216800492837855587645487)
	 (80400913152504619403090212798256673448651601777466684753786969417600730360353) 
	 (0x1)  


let test = 
	let scalar1 = createL sk1 in 
	let p1' =toAffineJ(montgomery_ladder basePoint scalar1) in 
	p1' = p1


(*
F = Zmod(115792089210356248762697446949407573530086143415290314195533631308867097853951)
E = EllipticCurve(F, [-3, 41058363725152142129326129780047268409114441015993725554835256314039467401291])

P = E(48439561293906451759052585252797914202762949526041747995844080717082404635286, 36134250956749795798585127919587881956611106672985015071877198253568414405109)

a = 256^7 + 256^6*142 + 256^5*187 + 256^4 * 185 + 256^3 * 94 + 256^2 * 237 + 256^1 * 14 + 19
Q = (a)*P

Q *)
