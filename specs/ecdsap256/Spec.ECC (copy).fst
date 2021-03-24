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


let pointAtInfinity #c : point_nat_prime #c  = (0, 0, 0)

let isPointAtInfinity (p:point_nat) =
  let (_, _, z) = p in z = 0



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

  (* if one point is at infinity, but not the second *)
  if pAffineZ <> qAffineZ then false else
  (* if two points are at infinity *)
  if pAffineZ = 0 && qAffineZ = 0 then true else
  (* if affine coordinates are equal *)
  if (pAffineX = qAffineX && pAffineY = qAffineY) then 
    true
  else false


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


let pointAdd #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  if pointEqual p q then 
    _point_double p 
  else
    _point_add p q



(*
val lemma_point_add_infinity: #c: curve ->
  p: point_nat_prime #c {~ (pointEqual p pointAtInfinity)} -> Lemma (_point_add #c p pointAtInfinity == p)
  
let lemma_point_add_infinity #c p = ()
*)


val _ml_step0: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step0 #c r0 r1 =
  let r0 = pointAdd r1 r0 in
  let r1 = pointAdd r1 r1 in
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




assume val lemmaPointAddR: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma 
  (pointEqual (pointAdd p q) (pointAdd q p))

assume val point_mult_infinity_as_repeat: #c: curve -> i: int {(i + 1) % getOrder #c = 0} -> p: point_nat_prime -> 
  Lemma (repeat (i % getOrder #c) (fun x -> pointAdd #c p x) p == pointAtInfinity)




val pointAddInfinity: #c: curve -> q: point_nat_prime #c -> Lemma (pointEqual (pointAdd pointAtInfinity q) q)

let pointAddInfinity #c q = ()

  
val pointAddAsAdd: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
    (requires (~ (pointEqual p q)))
    (ensures (pointAdd p q == _point_add p q))

let pointAddAsAdd #c p q = ()

val pointAddAsDouble: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
  (requires (True))
  (ensures (pointAdd p p == _point_double p))

let pointAddAsDouble #c p q = ()


assume val pointAddEqual: #c: curve -> p: point_nat_prime #c -> p1: point_nat_prime #c {pointEqual p p1} 
  -> q: point_nat_prime #c -> 
  Lemma (pointEqual (pointAdd p q) (pointAdd p1 q))



val point_mult: #c: curve -> i: int -> p: point_nat_prime #c -> point_nat_prime #c

let point_mult #c i p = 
  let i = (i - 1) % getOrder #c in 
  repeat i (fun x -> pointAdd #c p x) p

val point_mult_0: #c: curve -> p: point_nat_prime #c -> i: int {i % getOrder #c = 0} -> 
  Lemma (point_mult #c i p == pointAtInfinity)

let point_mult_0 #c p i = point_mult_infinity_as_repeat #c (getOrder #c - 1) p


val point_mult_1: #c: curve ->p: point_nat_prime #c ->  Lemma (point_mult #c 1 p == p)

let point_mult_1 #c p = 
  eq_repeat0 (fun x -> pointAdd #c p x) p 


val lemma_eq: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c {p == q} -> Lemma (pointEqual p q)

let lemma_eq #c p q = ()


val point_mult_ext: #c: curve -> i: int -> p: point_nat_prime #c -> Lemma (
  let f = (fun x -> pointAdd #c p x) in  
  pointEqual (f (point_mult #c i p)) (point_mult #c (i + 1) p))

let point_mult_ext #c i p = 
  let f = (fun x -> pointAdd #c p x) in 
  if i % getOrder #c = 0 then 
    begin
      point_mult_0 #c p i;
      pointAddInfinity p;
      lemmaPointAddR pointAtInfinity p;
      point_mult_1 #c p
    end
  else 
    begin
      unfold_repeat (getOrder #c) f p ((i - 1) % getOrder #c);
      lemma_mod_add_distr 1 (i - 1) (getOrder #c)
    end


assume val lemma_point_add : #c: curve -> p0: point_nat_prime #c -> pk: int -> qk: int -> i: int ->
  Lemma (
    let f = (fun x -> pointAdd #c p0 x) in 
    let p = pointAdd (point_mult pk p0) (point_mult qk p0) in 
    let p_i = pointAdd (point_mult (pk - i) p0) (point_mult (qk + i) p0) in 
    pointEqual p p_i)



val lemmaApplPointDouble: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: int
  -> p: point_nat_prime #c {pointEqual p (point_mult pk p0)} ->
  Lemma (
    let r = pointAdd p p in 
    pointEqual r (point_mult (2 * pk) p0))

let lemmaApplPointDouble #c p0 pk p =  
  let pk_p = point_mult pk p0 in 
  
  lemma_point_add #c p0 pk pk (pk - 1);
  point_mult_1 p0;
  point_mult_ext (2 * pk - 1) p0;

  pointAddEqual p pk_p pk_p;
  pointAddEqual p pk_p p 


val lemmaApplPointAdd: #c: curve -> p0: point_nat_prime #c 
  -> pk: int
  -> p: point_nat_prime #c {pointEqual p (point_mult pk p0)} 
  -> qk: int
  -> q: point_nat_prime #c {pointEqual q (point_mult qk p0)} -> 
  Lemma (
    let r = pointAdd p q in 
    pointEqual r (point_mult (pk + qk) p0))

let lemmaApplPointAdd #c p0 pk p qk q = 
  let pk_p = point_mult pk p0 in 
  let qk_p = point_mult qk p0 in 

  assert(pointEqual p (point_mult pk p0));
  assert(pointEqual q (point_mult qk p0));
  
  lemmaPointAddR pk_p qk_p;

  lemma_point_add #c p0 qk pk (qk - 1);
    assert(pointEqual (pointAdd pk_p qk_p) (pointAdd (point_mult 1 p0) (point_mult (pk + qk - 1) p0)));
  point_mult_1 p0;
  
  point_mult_ext (pk + qk - 1) p0; 
  pointAddEqual p pk_p qk_p;
  pointAddEqual q qk_p p;

  lemmaPointAddR p qk_p;
  lemmaPointAddR q p



val mlStep0AsPointAdd: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: nat
  -> p: point_nat_prime #c {pointEqual p (point_mult #c pk p0)}  
  -> qk: nat 
  -> q: point_nat_prime #c {pointEqual q (point_mult #c qk p0)} -> 
  Lemma
  (requires (~ (pointEqual p q)))
  (ensures (
    let p_i, q_i = _ml_step0 p q in 
    pointEqual p_i (point_mult #c (pk + qk) p0) /\
    pointEqual q_i (point_mult #c (2 * qk) p0)))


let mlStep0AsPointAdd #c p0 p_k p q_k q = 
    _ml_step0_lemma #c p q;
  let r0 = _point_add q p in
  let r1 = _point_double q in

  pointAddAsAdd p q;
  pointAddAsDouble q q;

  let f = (fun x -> pointAdd #c p0 x) in 
  
  assert(r0 == pointAdd q p);

  lemmaPointAddR p q; 
  lemmaApplPointAdd p0 p_k p q_k q;

  assert (r1 == pointAdd q q);
  lemmaApplPointDouble p0 q_k q



val mlStep1AsPointAdd: #c: curve
  -> p0: point_nat_prime #c
  -> pk: nat
  -> p: point_nat_prime #c {pointEqual p (point_mult #c pk p0)} 
  -> qk: nat 
  -> q: point_nat_prime #c {pointEqual q (point_mult #c qk p0)} -> 
  Lemma
  (requires (~ (pointEqual p q)))
  (ensures (
    let p_i, q_i = _ml_step1 p q in 
    pointEqual q_i (point_mult (pk + qk) p0) /\ 
    pointEqual p_i (point_mult (2 * pk) p0)))
      
let mlStep1AsPointAdd #c p0 pk p qk q = 
  let r1 = _point_add p q in
  let r0 = _point_double p in
  _ml_step1_lemma #c p q;

  pointAddAsAdd p q; 
  pointAddAsDouble p p;

  let f = (fun x -> pointAdd #c p0 x) in 
  
  assert (r1 == pointAdd p q);
  lemmaApplPointAdd p0 pk p qk q;

  assert (r0 == pointAdd p p);
  lemmaApplPointDouble p0 pk p



val point_mult_0_lemma: #c: curve -> p: point_nat_prime #c ->  Lemma (point_mult 1 p == p)

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
  -> i: tuple2 (point_nat_prime #c) (point_nat_prime #c) {
    let r0, r1 = i in ~ (pointEqual r0 r1) /\ 
    pointEqual r0 (point_mult #c 0 r1)} 
  -> o: tuple2 (point_nat_prime #c) (point_nat_prime #c) {
    let p, q = i in 
    let r0, r1 = o in ~ (pointEqual r0 r1) /\
    pointEqual r0 (point_mult (scalar_as_nat #c s) q)}


let montgomery_ladder_spec_left #c s (p0, q0) =
  let pred (i:nat {i <= getScalarLen c}) (r: tuple2 (point_nat_prime #c) (point_nat_prime #c)) = (
    let p_i, q_i = r in 
    ~ (pointEqual p_i q_i) /\
    pointEqual p_i (point_mult #c (scalar_as_nat_ #c s i) q0) /\
    pointEqual q_i (point_mult #c (scalar_as_nat_ #c s i + 1) q0)) in

  scalar_as_nat_0_lemma #c s;
  point_mult_0_lemma #c q0;

  assert (q0 == point_mult #c 1 q0);

  let r = repeati_inductive (getScalarLen c) pred
    (fun i out -> 

      let r = _ml_step s i out in  

      let p_i, q_i = out in 
      let bit = (getPower c - 1) - i in
      let bit = ith_bit s bit in

      let pk = scalar_as_nat_ #c s i in 

      mlStep0AsPointAdd q0 pk p_i (pk + 1) q_i;
      mlStep1AsPointAdd q0 pk p_i (pk + 1) q_i;

      scalar_as_nat_def #c s (i + 1);


      r) (p0, q0) in 

  r



val lemma_not_equal_to_infinity: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  Lemma (~ (pointEqual (0, 0, 0) p))

let lemma_not_equal_to_infinity #c p = ()


val scalar_multiplication: #c: curve -> scalar_bytes #c -> 
  p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  point_nat_prime #c 

let scalar_multiplication #c k p =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c p;
    point_mult_0_lemma #c p;

  let q, f = montgomery_ladder_spec_left k (pai, p) in
  _norm #c q


val secret_to_public: #c: curve -> scalar_bytes #c -> (point_nat_prime #c)

let secret_to_public #c k =
  let pai = (0, 0, 0) in
    lemma_not_equal_to_infinity #c (basePoint #c);
  let q, f = montgomery_ladder_spec_left #c k (pai, (basePoint #c)) in
  _norm #c q

