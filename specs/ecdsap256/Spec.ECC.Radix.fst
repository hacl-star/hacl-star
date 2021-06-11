module Spec.ECC.Radix

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

open Lib.LoopCombinators 

open FStar.Math.Lemmas
open FStar.Math.Lib

open Spec.ECC.Curves

open Spec.ECC


#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let radix = 4

val getPrecomputedPoint: #c: curve -> p: point_nat_prime #c -> i: nat -> 
  Tot (r: point_nat_prime #c {pointEqual r (point_mult i p)})

let getPrecomputedPoint #c p i = 
  point_mult i p


val _ml_step: #c: curve -> k: scalar_bytes #c 
  -> p0: point_nat_prime #c  
  -> i: nat{i < v (getScalarLen c)} 
  -> p: point_nat_prime #c
  -> point_nat_prime #c

let _ml_step #c k p0 i p =
  let s = scalar_as_nat k in 
  let si = (arithmetic_shift_right s (i * radix)) % (pow2 radix) in 
  let pointPrecomputed = getPrecomputedPoint p0 si in 

  (* lazy version *)
  let p2 = _point_double p in 
  let p4 = _point_double p2 in 
  let p8 = _point_double p4 in 
  let p16 = _point_double p8 in
  
  _point_add pointPrecomputed p16



assume val pred0: #c: curve -> x: point_nat_prime #c -> s: scalar_bytes #c ->
  p: point_nat_prime #c -> i: nat {i < v (getScalarLen c)} ->
  Lemma (True)

val lemma_predicate0: #c: curve -> s: scalar_bytes #c -> p0: point_nat_prime #c -> 
  Lemma (
    let len = (v (getScalarLen c) - 1) / 4  in 
    let f = _ml_step #c s p0 in
    let pred (i: nat) p : Type0 = (
      let scalar = scalar_as_nat s in 
      let partialScalar = scalar % (pow2 (4 * (i + 1))) in 
      pointEqual p (point_mult #c partialScalar p0)) in 
    forall (i: nat {i < len}) (x: point_nat_prime #c). 
    pred i x ==> pred (i + 1) (f i x))

let lemma_predicate0 #c s p0 = 
  let pred = pred0 #c in
  admit();
  Classical.forall_intro_4 pred


val scalar_as_nat_upperbound_: #c: curve -> s: scalar_bytes #c ->
  i: nat {i >= 0 /\ i <= v (getScalarLen c)} ->
  Lemma (scalar_as_nat_ s i < pow2 i)

let scalar_as_nat_upperbound_ #c s i = 
  match i with 
  |0 -> scalar_as_nat_zero s
  |_ -> admit()


val lemma_scalar_as_nat_upperbound: #c: curve -> s: scalar_bytes #c -> Lemma (scalar_as_nat s < pow2 (v (getScalarLen c)))

let lemma_scalar_as_nat_upperbound #c s = scalar_as_nat_upperbound_ s (v (getScalarLen c))


val radix_spec: #c: curve -> s: scalar_bytes #c {v (getScalarLen c) % 4 == 0}
  -> i: point_nat_prime #c
  -> r: point_nat_prime #c {
    let pointStart = getPrecomputedPoint i (scalar_as_nat s % pow2 4) in 
    r == repeati ((v (getScalarLen c) - 1) / 4) (_ml_step #c s i) pointStart /\ 
    pointEqual r (point_mult (scalar_as_nat #c s) i)}


let radix_spec #c s p0 = 
  let scalarNat = scalar_as_nat s in 
  let pointToStart = getPrecomputedPoint p0 (scalarNat % pow2 4) in 

  let len =  (v (getScalarLen c) - 1) / 4 in 
  
  let pred (i: nat {i <= len}) p : Type0 = (
    let scalar = scalar_as_nat s in 
    let partialScalar = scalar % (pow2 (4 * (i + 1))) in 
    pointEqual p (point_mult #c partialScalar p0)) in 

  let f = _ml_step #c s p0 in 
  
  lemma_predicate0 s p0; 
  let r = repeati_inductive' #(point_nat_prime #c) len pred f pointToStart in 

  lemma_scalar_as_nat_upperbound #c s;
  small_mod (scalar_as_nat s) (pow2 (v (getScalarLen c)));
  r



