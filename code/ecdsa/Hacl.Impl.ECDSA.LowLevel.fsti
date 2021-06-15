module Hacl.Impl.ECDSA.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition

open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul

inline_for_extraction noextract
val reduction_prime_2prime_with_carry: #c: curve -> x: widefelem c -> result: felem c ->
  Stack unit 
  (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat c h x < 2 * getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = wide_as_nat c h0 x % getOrder #c)  

inline_for_extraction noextract
val reduction_prime_2prime_order: #c: curve -> x: felem c -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result == as_nat c h0 x % getOrder #c)  

inline_for_extraction noextract
val felem_add: #c: curve -> a: felem c -> b: felem c -> out: felem c ->
  Stack unit
  (requires (fun h0 ->
    live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat c h0 a < getOrder #c /\ as_nat c h0 b < getOrder #c))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat c h1 out == (as_nat c h0 a + as_nat c h0 b) % getOrder #c /\
    as_nat c h1 out == toDomain_ #c #DSA ((fromDomain_ #c #DSA (as_nat c h0 a) + fromDomain_ #c #DSA (as_nat c h0 b)) % getOrder #c)))


inline_for_extraction noextract
val upload_one_montg_form: #c: curve -> b: felem c -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat c h1 b = toDomain_ #c #DSA 1)
