module Hacl.Impl.ECDSA.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition

open FStar.Mul


val reduction_prime_2prime_with_carry: #c: curve -> x: widefelem c -> result: felem c ->
  Stack unit 
  (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat c h x < 2 * getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = wide_as_nat c h0 x % getOrder #c)  

val reduction_prime_2prime_order: #c: curve -> x: felem c -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result == as_nat c h0 x % getOrder #c)  

