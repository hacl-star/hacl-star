module Spec.ECC.ML

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.LoopCombinators 

open Spec.ECC.Curves
open Spec.ECC

open FStar.Math.Lemmas
open Spec.ECC.ML.Lemmas

open FStar.Mul


#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

val _ml_step0: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c) 

let _ml_step0 #c r0 r1 =
  let r0 = pointAdd r1 r0 in
  let r1 = pointAdd r1 r1 in
  (r0, r1)


val _ml_step1: #c: curve -> r0: point_nat_prime #c -> r1: point_nat_prime #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step1 #c r0 r1 =
  let r1 = pointAdd r0 r1 in
  let r0 = pointAdd r0 r0 in
  (r0, r1)


val _ml_step: #c: curve -> k: scalar_bytes #c -> i: nat{i < v (getScalarLen c)} 
  -> r: tuple2 (point_nat_prime #c) (point_nat_prime #c)
  -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step #c k i (p, q) =
  let bit = v (getScalarLen c) - 1 - i in
  let bit = ith_bit k bit in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q


val mlStep0AsPointAdd: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: nat
  -> p: point_nat_prime #c {pointEqual p (point_mult #c pk p0)}  
  -> qk: nat 
  -> q: point_nat_prime #c {pointEqual q (point_mult #c qk p0)} -> 
  Lemma
  (ensures (
    let p_i, q_i = _ml_step0 p q in 
    pointEqual p_i (point_mult #c (pk + qk) p0) /\
    pointEqual q_i (point_mult #c (2 * qk) p0)))


let mlStep0AsPointAdd #c p0 p_k p q_k q = 
  curve_commutativity_lemma p q; 
  lemmaApplPointAdd p0 p_k p q_k q;
  lemmaApplPointDouble p0 q_k q


val mlStep1AsPointAdd: #c: curve
  -> p0: point_nat_prime #c
  -> pk: nat
  -> p: point_nat_prime #c {pointEqual p (point_mult #c pk p0)} 
  -> qk: nat 
  -> q: point_nat_prime #c {pointEqual q (point_mult #c qk p0)} -> 
  Lemma
  (ensures (
    let p_i, q_i = _ml_step1 p q in 
    pointEqual q_i (point_mult (pk + qk) p0) /\ 
    pointEqual p_i (point_mult (2 * pk) p0)))
      
let mlStep1AsPointAdd #c p0 pk p qk q = 
  lemmaApplPointAdd p0 pk p qk q;
  lemmaApplPointDouble p0 pk p


val scalar_as_nat_: #c: curve -> scalar_bytes #c -> i: nat {i <= v (getScalarLen c)} -> nat

let rec scalar_as_nat_ #c s i = 
  if i = 0 then 0 else 
  let bit = ith_bit s (v (getScalarLen c) - i) in 
  scalar_as_nat_ #c s (i - 1) * 2 + uint_to_nat bit 

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val scalar_as_nat_zero: #c: curve -> s: scalar_bytes #c ->  Lemma (scalar_as_nat_ s 0 == 0)

let scalar_as_nat_zero #c s = ()


val scalar_as_nat_def: #c: curve -> s: scalar_bytes #c -> i: nat {i > 0 /\ i <= v (getScalarLen c)} -> Lemma (
  scalar_as_nat_ #c s i == 2 * scalar_as_nat_ #c s (i - 1) + uint_to_nat (ith_bit s (v (getScalarLen c) - i)))

let scalar_as_nat_def #c s i = ()


val scalar_as_nat: #c: curve -> scalar_bytes #c -> nat

let scalar_as_nat #c s = scalar_as_nat_ #c s (v (getScalarLen c))



val montgomery_ladder_spec_left: #c: curve -> s: scalar_bytes #c 
  -> i: tuple2 (point_nat_prime #c) (point_nat_prime #c) {let i0, i1 = i in pointEqual i0 (point_mult #c 0 i1)} 
  -> r: tuple2 (point_nat_prime #c) (point_nat_prime #c) {
    let r0, r1 = r in let i0, i1 = i in
    r == repeati (v (getScalarLen c)) (_ml_step #c s) i /\
    pointEqual r0 (point_mult (scalar_as_nat #c s) i1)}


val pred0: #c: curve -> x: tuple2 (point_nat_prime #c) (point_nat_prime #c) -> s: scalar_bytes ->
  p: tuple2 (point_nat_prime #c) (point_nat_prime #c) -> i: nat {i < v (getScalarLen c)} ->
  Lemma (
    let f = _ml_step #c s in 
    let pred i r =  
      let p_i, q_i = r in 
      let p0, q0 = p in 
      let si = scalar_as_nat_ #c s i in 
      let si1 = scalar_as_nat_ #c s i + 1 in
      pointEqual p_i (point_mult #c si q0) /\ pointEqual q_i (point_mult #c si1 q0)  in 
    (pred i x ==> pred (i + 1) (f i x))) 

let pred0 #c x s p i =  (*
      let pk = scalar_as_nat_ #c s i in 
      assume (pointEqual p_i (point_mult pk p0));
      assume (pointEqual q_i (point_mult (pk + 1) p0));
      admit();
      mlStep0AsPointAdd q0 pk p_i (pk + 1) q_i; admit();
      mlStep1AsPointAdd q0 pk p_i (pk + 1) q_i; 
      scalar_as_nat_def #c s (i + 1);  *) admit()


val lemma_predicate0:  #c: curve ->  s: scalar_bytes 
  -> p: tuple2 (point_nat_prime #c) (point_nat_prime #c) -> 
  Lemma (
    let f = _ml_step #c s in 
    let pred i r =  
      let p_i, q_i = r in 
      let p0, q0 = p in 
      let si = scalar_as_nat_ #c s i in 
      let si1 = scalar_as_nat_ #c s i + 1 in
      pointEqual p_i (point_mult #c si q0) /\ pointEqual q_i (point_mult #c si1 q0)  in 
    forall (i:nat{i < v (getScalarLen c)}) (x: (tuple2 (point_nat_prime #c) (point_nat_prime #c))). 
    pred i x ==> pred (i + 1) (f i x))

let lemma_predicate0 #c s p = 
  let pred = pred0 #c in
  Classical.forall_intro_4 pred


let montgomery_ladder_spec_left #c s (p0, q0) = 
  let len : nat  = v (getScalarLen c) in 
  
  let pred i r = (
    let p_i, q_i = r in 
    let si = scalar_as_nat_ #c s i in 
    let si1 = scalar_as_nat_ #c s i + 1 in
    pointEqual p_i (point_mult #c si q0) /\
    pointEqual q_i (point_mult #c si1 q0)) in
    
  let f = _ml_step #c s in 

  lemma_predicate0 s (p0, q0);
  point_mult_0_lemma #c q0;
  repeati_inductive' #(tuple2 (point_nat_prime #c) (point_nat_prime #c)) len pred f (p0, q0)

#pop-options


val scalar_multiplication: #c: curve -> scalar_bytes #c -> 
  p: point_nat_prime #c {~ (isPointAtInfinity p)} -> 
  point_nat_prime #c 

let scalar_multiplication #c k p =
  point_mult_0 p 0; 
  let q, f = montgomery_ladder_spec_left k (pointAtInfinity, p) in
  _norm #c q

val secret_to_public: #c: curve -> scalar_bytes #c -> (point_nat_prime #c)

let secret_to_public #c k =
  point_mult_0 (basePoint #c) 0;
  let q, f = montgomery_ladder_spec_left #c k (pointAtInfinity, (basePoint #c)) in
  _norm #c q

