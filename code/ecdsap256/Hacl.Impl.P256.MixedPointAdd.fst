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


#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"


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


val copy_conditional_one_mm: out: felem -> mask: uint64 -> Stack unit
  (requires fun h -> as_nat h out < prime256 /\ live h out /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < prime256 /\ (
    if v mask = 0
      then as_nat h1 out == as_nat h0 out
      else 
	as_nat h1 out == Spec.P256.MontgomeryMultiplication.toDomain_ 1  ))

let copy_conditional_one_mm out mask = 
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = u64 1 in 
  let x_1 = u64 18446744069414584320 in 
  let x_2 = u64 18446744073709551615 in 
  let x_3 = u64 4294967294 in 

  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 

  lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask;

  upd out (size 0) r_0;
  upd out (size 1) r_1;
  upd out (size 2) r_2;
  upd out (size 3) r_3;

  Spec.P256.MontgomeryMultiplication.lemmaToDomain 1;
  assert_norm(pow2 256 % prime256 = uint_v x_0 + uint_v x_1 * pow2 64 + uint_v x_2 * pow2 128 + uint_v x_3 * pow2 192);
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192)


val copy_point_conditional: out: point -> p: pointAffine -> maskPoint: point -> Stack unit 
  (requires fun h -> live h out /\ live h p /\ live h maskPoint /\ 
    disjoint p out /\ disjoint p maskPoint /\ disjoint out maskPoint /\
    (
      let xOut = as_nat h (gsub out (size 0) (size 4)) in 
      let yOut = as_nat h (gsub out (size 4) (size 4)) in 
      let zOut = as_nat h (gsub out (size 8) (size 4)) in 
      xOut < prime256 /\ yOut < prime256 /\ zOut < prime256 /\
      as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime256
    )
  )
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let xOut = gsub out (size 0) (size 4) in 
    let yOut = gsub out (size 4) (size 4) in 
    let zOut = gsub out (size 8) (size 4) in 
    as_nat h1 xOut < prime256 /\
    as_nat h1 yOut < prime256 /\
    as_nat h1 zOut < prime256 /\ (
    
    let mask = as_nat h0 (gsub maskPoint (size 8) (size 4)) in 
    let x = gsub p (size 0) (size 4) in 
    let y = gsub p (size 4) (size 4) in 

    if mask = 0 then 
      as_nat h1 xOut == as_nat h0 x /\ 
      as_nat h1 yOut == as_nat h0 y /\ 
      as_nat h1 zOut == Spec.P256.MontgomeryMultiplication.toDomain_ 1 
    else 
      as_nat h1 xOut == as_nat h0 xOut /\ 
      as_nat h1 yOut == as_nat h0 yOut /\ 
      as_nat h1 zOut == as_nat h0 zOut 
    )))

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
  copy_conditional_one_mm zOut mask


(* we except that we already know the q point *)
val pointAddMixed: result: point -> p: point -> q: pointAffine -> Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h q)
  (ensures fun h0 _ h1 -> True)


let pointAddMixed result p q = 
  copy_point_conditional result q p
