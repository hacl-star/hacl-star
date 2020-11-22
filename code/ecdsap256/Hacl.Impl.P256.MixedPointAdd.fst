module Hacl.Impl.P256.MixedPointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.PointAdd



inline_for_extraction
type pointAffine = lbuffer uint64 (size 8)

val pointAffineIsNotZero: p: pointAffine -> Stack uint64
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      if as_nat h0 x = 0 || as_nat h0 y = 0 then uint_v r = pow2 64 - 1 else uint_v r == 0))
  

let pointAffineIsNotZero p = 
  let x = sub p (size 0) (size 4) in 
  let y = sub p (size 4) (size 4) in 
  let xZero = isZero_uint64_CT x in 
  let yZero = isZero_uint64_CT y in 
  logor_lemma xZero yZero;
  logor xZero yZero


val copy_point_conditional: out: point -> p: pointAffine -> maskPoint: point -> Stack unit 
  (requires fun h -> live h out /\ live h p /\ live h maskPoint /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc p |+| loc out |+| loc maskPoint] /\
    (
      let xOut = as_nat h (gsub out (size 0) (size 4)) in 
      let yOut = as_nat h (gsub out (size 4) (size 4)) in 
      let zOut = as_nat h (gsub out (size 8) (size 4)) in 
      xOut < prime256 /\ yOut < prime256 /\ zOut < prime256 /\
      as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime256
    )
  )
  (ensures fun h0 _ h1 -> True) 

let copy_point_conditional out p maskPoint = 
  let z = sub maskPoint (size 8) (size 4) in 
  let mask = isZero_uint64_CT z in 

  let xOut = sub out (size 0) (size 4) in 
  let yOut = sub out (size 4) (size 4) in 
  let zOut = sub out (size 8) (size 4) in 

  let p_x = sub p (size 0) (size 4) in 
  let p_y = sub p (size 4) (size 4) in 

  copy_conditional xOut p_x mask;
  copy_conditional yOut p_y mask;
  (* 1 should be in Domaine*)
  copy_conditional zOut (u64 1) mask


(* we except that we already know the q point *)
val pointAddMixed: result: point -> p: point -> q: pointAffine -> Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h q)
  (ensures fun h0 _ h1 -> True)


let pointAddMixed result p q = 
  copy_point_conditional result q p
