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

let ith_bit (#c: curve) (k: scalar_bytes #c) (i:nat{i < getScalarLen c}) : (r: uint64 {v r == 0 \/ v r == 1}) =
  let q = (v (getScalarLenBytes c) - 1) - i / 8 in 
  let r = size (i % 8) in
  logand_mask (index k q >>. r) (u8 1) 1;
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


val pointAddAsAdd: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
    (requires (~ (pointEqual p q)))
    (ensures (pointAdd p q == _point_add p q))

let pointAddAsAdd #c p q = ()

val pointAddAsDouble: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
  (requires (True))
  (ensures (pointAdd p p == _point_double p))

let pointAddAsDouble #c p q = ()


(*  *)
val point_mult: #c: curve -> i: nat {i > 0} -> p: point_nat_prime #c -> point_nat_prime #c

let point_mult #c i p = repeat (i - 1) (fun x -> pointAdd #c p x) p


assume val lemmaPointAddR: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma 
  (pointAdd p q == pointAdd q p)
  


assume val lemma_point_add : #c: curve -> p0: point_nat_prime #c -> pk: nat
  -> i: nat {i <= pk} ->
  Lemma (
   let f = (fun x -> pointAdd #c p0 x) in 
   pointAdd (repeat pk f p0) (repeat pk f p0) == pointAdd (repeat (pk + i) f p0) (repeat (pk - i) f p0))



val lemmaApplPointDouble: #c: curve -> p0: point_nat_prime #c -> pk: pos -> p: point_nat_prime #c {p == point_mult pk p0} ->
  Lemma (
    let r = pointAdd p p in 
    let f = (fun x -> pointAdd #c p0 x) in 
    r == point_mult (2 * pk) p0)

let lemmaApplPointDouble #c p0 pk p = 
  let f = (fun x -> pointAdd #c p0 x) in 

  lemma_point_add #c p0 (pk - 1) (pk  - 1);
  eq_repeat0 f p0;
  
  lemmaPointAddR (repeat (2 * pk - 2) f p0) p0;
  unfold_repeat (2 * pk) f p0 (2 * pk - 2)



val mlStep0AsPointAdd: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: pos
  -> p: point_nat_prime #c {p == point_mult #c pk p0}  
  -> qk: pos
  -> q: point_nat_prime #c {q == point_mult #c qk p0} -> 
  Lemma
    (requires (~ (pointEqual p q)))
    (ensures (
      let p_i, q_i = _ml_step0 p q in 
      (*p_i == repeat (pk + qk) (fun x -> pointAdd #c p0 x) p0 /\ *)
      p_i == point_mult #c (pk + qk) p0 /\
     (* q_i == repeat (2 * qk) (fun x -> pointAdd #c p0 x) p0 /\  *)
      q_i == point_mult #c (2 * qk) p0
  ))


let mlStep0AsPointAdd #c p0 p_k p q_k q = 
    _ml_step0_lemma #c p q;
  let r0 = _point_add q p in
  let r1 = _point_double q in

  pointAddAsAdd p q;
  pointAddAsDouble q q;

  let f = (fun x -> pointAdd #c p0 x) in 
  
  assert(r0 == pointAdd q p);
  assume(r0 == repeat (p_k + q_k - 1) f p0);

  assert (r1 == pointAdd q q);
  lemmaApplPointDouble p0 q_k q



val mlStep1AsPointAdd: #c: curve
  -> p0: point_nat_prime #c
  -> pk: pos
  -> p: point_nat_prime #c {p == point_mult #c pk p0} 
  -> qk: pos
  -> q: point_nat_prime #c {q == point_mult #c qk p0} -> 
  Lemma
    (requires (~ (pointEqual p q)))
    (ensures (
      let p_i, q_i = _ml_step1 p q in 
      (* q_i == repeat (pk + qk) (fun x -> pointAdd #c p0 x) p0 /\ *)
      q_i == point_mult (pk + qk) p0 /\ 
      (*p_i == repeat (2 * pk) (fun x -> pointAdd #c p0 x) p0 /\ *)
      p_i == point_mult (2 * pk) p0
  ))
     
      
let mlStep1AsPointAdd #c p0 pk p qk q = 
  let r1 = _point_add p q in
  let r0 = _point_double p in
  _ml_step1_lemma #c p q;

  pointAddAsAdd p q; 
  pointAddAsDouble p p;

  let f = (fun x -> pointAdd #c p0 x) in 
  
  assert (r1 == pointAdd p q);
  assume (r1 == repeat (pk + qk - 1) f p0);

  assert (r0 == pointAdd p p);
  lemmaApplPointDouble p0 pk p



val point_mult_0_lemma: #c: curve -> p: point_nat_prime #c ->  Lemma (point_mult 0 p == p)

let point_mult_0_lemma #c p = 
  Lib.LoopCombinators.eq_repeat0 (fun x -> pointAdd #c p x) p 


val scalar_as_nat_: #c: curve -> scalar_bytes #c -> i: nat {i <= getScalarLen c} -> nat

let rec scalar_as_nat_ #c s i = 
  if i = 0 then 0 else 
  let bit = ith_bit s (getScalarLen c - i) in 
  scalar_as_nat_ #c s (i - 1) * 2 + uint_to_nat bit 

val scalar_as_nat_def: #c: curve -> s: scalar_bytes #c -> i: nat {i > 0 /\ i <= getScalarLen c} -> Lemma (
  scalar_as_nat_ #c s i == 2 * scalar_as_nat_ #c s (i - 1) +  uint_to_nat (ith_bit s (getScalarLen c - i)))

let scalar_as_nat_def #c s i = ()


val scalar_as_nat: #c: curve -> scalar_bytes #c -> nat

let scalar_as_nat #c s = scalar_as_nat_ #c s (getScalarLen c)


val scalar_as_nat_0_lemma: #c: curve -> s: scalar_bytes #c -> Lemma (scalar_as_nat_ #c s 0 == 0)

let scalar_as_nat_0_lemma #c s = ()


val montgomery_ladder_spec_left: #c: curve -> s: scalar_bytes #c 
  -> i: tuple2 (point_nat_prime #c) (point_nat_prime #c) 
    {let r0, r1 = i in ~ (pointEqual r0 r1) /\ r1 == point_mult #c 1 r0} 
  -> o: tuple2 (point_nat_prime #c) (point_nat_prime #c) {
    let p, q = i in 
    let r0, r1 = o in ~ (pointEqual r0 r1) /\
    r0 == point_mult (scalar_as_nat #c s) p} 


let montgomery_ladder_spec_left #c s pq =
  let pred (i:nat {i <= getScalarLen c}) (p: tuple2 (point_nat_prime #c) (point_nat_prime #c)) = (
    let p0, q0 = pq in 
    let p_i, q_i = p in  ~ (pointEqual p_i q_i) /\
    p_i == point_mult #c (scalar_as_nat_ #c s i) p0 /\
    q_i == point_mult #c (scalar_as_nat_ #c s i + 1) p0) in

  let p0, q0 = pq in 
  scalar_as_nat_0_lemma #c s;
  point_mult_0_lemma #c p0;

  let r = repeati_inductive (getScalarLen c) pred
    (fun i out -> 
      let r = _ml_step s i out in  

      let p_i, q_i = out in 
      let bit = (getPower c - 1) - i in
      let bit = ith_bit s bit in
      
      let pk = scalar_as_nat_ #c s i in 

      mlStep0AsPointAdd p0 pk p_i (pk + 1) q_i;
      mlStep1AsPointAdd p0 pk p_i (pk + 1) q_i;

      scalar_as_nat_def #c s (i + 1);

      r) pq in 
  r



assume val lemma_not_equal_to_infinity: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  Lemma (~ (pointEqual (0, 0, 0) p))


val scalar_multiplication: #c: curve -> scalar_bytes #c -> 
  p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  point_nat_prime #c 

let scalar_multiplication #c k p =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c p;
  let q, f = montgomery_ladder_spec_left k (pai, p) in
  _norm #c q


val secret_to_public: #c: curve -> scalar_bytes #c -> (point_nat_prime #c)

let secret_to_public #c k =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c (basePoint #c);
  let q, f = montgomery_ladder_spec_left #c k (pai, (basePoint #c)) in
  _norm #c q

