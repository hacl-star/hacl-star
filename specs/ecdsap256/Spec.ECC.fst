module Spec.ECC

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

open Lib.LoopCombinators 

open FStar.Math.Lemmas
open FStar.Math.Lib

open Spec.ECC.Curves

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


noextract
let _point_double #curve (p:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let x, y, z = p in
  let delta = z * z in 
  let gamma = y * y in 
  let beta = x * gamma in 
  let alpha = 3 * (x - delta) * (x + delta) in 
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha * (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = ((y + z) * (y + z) - delta - gamma) % prime in 
  (x3, y3, z3)


let isPointAtInfinity (p:point_nat) =
  let (_, _, z) = p in z = 0


#push-options "--fuel 1"

let _norm #curve (p:point_nat_prime #curve) : (point_nat_prime #curve) =
  let prime = getPrime curve in 
  let (x, y, z) = p in
  let z2 = z * z in
  let z2i = modp_inv2_pow #curve z2 in
  let z3 = z * z * z in
  let z3i = modp_inv2_pow #curve z3 in
  let x3 = (z2i * x) % prime in
  let y3 = (z3i * y) % prime in
  let z3 = if isPointAtInfinity p then 0 else 1 in
  (x3, y3, z3)


let scalar_bytes (#c: curve) = lbytes (v (getScalarLenBytes c))

let ith_bit (#c: curve) (k: scalar_bytes #c) (i:nat{i < getScalarLen c}) : uint64 =
  let q = (v (getScalarLenBytes c) - 1) - i / 8 in 
  let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)
  

let isPointOnCurve (#c: curve) (p: point_nat_prime #c) : bool = 
  let (x, y, z) = p in
  (y * y) % (getPrime c) =
  (x * x * x + aCoordinate #c  * x + bCoordinate #c) % prime256


val toJacobianCoordinates: tuple2 nat nat -> tuple3 nat nat nat

let toJacobianCoordinates (r0, r1) = (r0, r1, 1)


let pointEqual #curve (p: point_nat_prime #curve) (q: point_nat_prime #curve) = 
  let pAffineX, pAffineY, pAffineZ = _norm p in 
  let qAffineX, qAffineY, qAffineZ = _norm q in 

  (* we try to present points in equality without infinity *)
  (*if isPointAtInfinity (p <: point_nat) && isPointAtInfinity (p <: point_nat) then 
    true
  else *)
    if (pAffineX = qAffineX && pAffineY = qAffineY) = false then 
      false
    else 
      true


noextract
let _point_add #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve {~ (pointEqual p q)}) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 * z2 in
  let z1z1 = z1 * z1 in

  let u1 = x1 * z2z2 % prime in
  let u2 = x2 * z1z1 % prime in

  let s1 = y1 * z2 * z2z2 % prime in
  let s2 = y2 * z1 * z1z1 % prime in

  let h = (u2 - u1) % prime in
  let r = (s2 - s1) % prime in

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3 = (rr - hhh - 2 * u1 * hh) % prime in
  let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime in
  let z3 = (h * z1 * z2) % prime in
  if z2 = 0 then
    (x1, y1, z1)
  else
    if z1 = 0 then
      (x2, y2, z2)
    else
      (x3, y3, z3)


val _ml_step0_lemma: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime {~ (pointEqual r0 r1)} -> Lemma (
  let r2 = _point_add r1 r0 in 
  let r3 = _point_double r1 in 
  ~ (pointEqual r2 r3))

let _ml_step0_lemma #c r0 r1 = 
  let r0x, r0y, r0z = r0 in 
  let r1x, r1y, r1z = r1 in 

  let r2 = _point_add r1 r0 in 
  let r3 = _point_double r1 in 

  let r2x, r2y, r2z = _point_add r1 r0 in  
  let r3x, r3y, r3z = _point_double r0 in 


  assume (~ (pointEqual (_point_add r1 r0) (_point_double r1)))




val _ml_step0: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c {~ (pointEqual r0 r1)} 
  -> r: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let r0, r1 = r in ~ (pointEqual r0 r1)}

let _ml_step0 #c r0 r1 =
    _ml_step0_lemma #c r0 r1;
  let r0 = _point_add r1 r0 in
  let r1 = _point_double r1 in
  (r0, r1)


assume val _ml_step1_lemma: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c {~ (pointEqual r0 r1)} -> Lemma (
  let r2 = _point_add r0 r1 in
  let r3 = _point_double r0 in
  ~ (pointEqual r2 r3))
    

val _ml_step1: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c {~ (pointEqual r0 r1)} -> 
  r: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let r0, r1 = r in ~ (pointEqual r0 r1)}

let _ml_step1 #c r0 r1 =
  let r3 = _point_add r0 r1 in
  let r2 = _point_double r0 in
  _ml_step1_lemma #c r0 r1;
  (r2, r3)


val _ml_step: #c: curve -> k:scalar_bytes #c -> i:nat{i < getScalarLen c} 
  -> r: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let r0, r1 = r in ~ (pointEqual r0 r1)} 
  -> r: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let r0, r1 = r in ~ (pointEqual r0 r1)} 

let _ml_step #c k i (p, q) =
  let bit = (getPower c - 1) - i in
  let bit = ith_bit k bit in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q





let pointAdd #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  if pointEqual p q then 
    _point_double p 
  else
    _point_add p q


val point_mult: #c: curve -> i: nat -> p: point_nat_prime #c -> point_nat_prime #c

let point_mult #c i p = repeat i (fun x -> pointAdd #c p x) p 


val scalar_as_nat_: #c: curve -> scalar_bytes #c -> i: nat {i <= v (getScalarLenBytes c)} -> nat

let rec scalar_as_nat_ #c s i = 
  if i = 0 then 0 else 
  let bit = ith_bit s i in 
  scalar_as_nat_ #c s (i - 1) +  pow2 (1 * (i - 1)) * uint_to_nat bit 


val scalar_as_nat: #c: curve -> scalar_bytes #c -> nat

let scalar_as_nat #c s = scalar_as_nat_ #c s (v (getScalarLenBytes c))



val montgomery_ladder_spec: #c: curve -> s: scalar_bytes #c 
  -> i: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let r0, r1 = i in ~ (pointEqual r0 r1)} -> 
  o: tuple2 (point_nat_prime #c) (point_nat_prime #c) {
    let p, q = i in 
    let r0, r1 = o in ~ (pointEqual r0 r1) /\
    r0 == point_mult (scalar_as_nat #c s) p} 


let montgomery_ladder_spec #c s pq =
  let pred (i:nat) (p: tuple2 (point_nat_prime #c) (point_nat_prime #c)) = (
    let p0, q0 = pq in 
    let p_i, q_i = p in  ~ (pointEqual p_i q_i) /\
    p_i == point_mult #c (scalar_as_nat_ #c s i) p0 /\
    q_i == point_mult #c (scalar_as_nat_ #c s (i + 1)) p0
    
    ) in

  assume (pred 0 pq);

  let r = repeati_inductive (getScalarLen c) pred
    (fun i out -> 
      let r = _ml_step s i out in  
      admit(); r) pq in 

  assert(
    let p_i1, q_i1 = r in ~ (pointEqual p_i1 q_i1));

  admit();
  r



assume val lemma_not_equal_to_infinity: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  Lemma (~ (pointEqual (0, 0, 0) p))


val scalar_multiplication: #c: curve -> scalar_bytes #c -> 
  p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  point_nat_prime #c 

let scalar_multiplication #c k p =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c p;
  let q, f = montgomery_ladder_spec k (pai, p) in
  _norm #c q


val secret_to_public: #c: curve -> scalar_bytes #c -> (point_nat_prime #c)

let secret_to_public #c k =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c (basePoint #c);
  let q, f = montgomery_ladder_spec #c k (pai, (basePoint #c)) in
  _norm #c q




(*
point_mult: i: nat -> p: point -> q: point 
point_mult i p q = 
 repeat i (pointAdd p) p


Add == _add <==> p <> q


for: 

inv0 = k == 0/ j == 1

 1) p_i = point_mul (k = as_nat i scalar) p 
 2) q_i = point_mul (j = as_nat i scalar + 1) p
 3) as_nat i scalar != as_nat i scalar + 1

 assume (p == q iff point_mult (as_nat i scalar % order) p == point_mult (as_nat i scalar  % order) q)

 if b = 0 then 
  add (-> Add) 
  double (-> Add) 

 else 
  add (-> add) 
  double (-> Add) *)
