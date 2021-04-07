module Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.ECDSA.Definition
open Spec.ECDSA
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.EC.Setup
open Hacl.Spec.EC.Definition

open FStar.Mul

noextract
let prime = (getOrder #P256)

val reduction_prime_2prime_with_carry: #c: curve -> x: widefelem c -> result: felem c ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat c h x < 2 * (getOrder #P256))
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = wide_as_nat c h0 x % (getOrder #P256))  


inline_for_extraction noextract
val reduction_prime_2prime_with_carry2: #c: curve ->  carry: uint64 ->  x: felem c 
  -> result: felem c ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ 
      uint_v carry * pow2 256 + as_nat c h x < 2 * (getOrder #P256) )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      as_nat c h1 result = (uint_v carry * pow2 256 + as_nat c h0 x) % (getOrder #P256))  


val reduction_prime_2prime_order: #c: curve -> x: felem c 
  -> result: felem c -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  as_nat c h1 result == as_nat c h0 x % (getOrder #P256))  

