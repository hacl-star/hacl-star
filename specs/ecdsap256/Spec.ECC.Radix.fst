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

val lemma_predicate0:  #c: curve -> s: scalar_bytes #c -> p: point_nat_prime #c -> 
  Lemma (True)

let lemma_predicate0 #c s p = 
  let pred = pred0 #c in
  Classical.forall_intro_4 pred


val radix_spec: #c: curve -> s: scalar_bytes #c 
  -> i: point_nat_prime #c
  -> r: point_nat_prime #c {
    (* r == repeati (v (getScalarLen c)) (_ml_step #c s) i /\ *)
    pointEqual r (point_mult (scalar_as_nat #c s) i)}


let radix_spec #c s i = 
  let len : nat  = v (getScalarLen c) in 
  
  let pred i r = True in
    
  let f = _ml_step #c s i in 

  lemma_predicate0 s i;
  admit();
  repeati_inductive' #(point_nat_prime #c) len pred f i

