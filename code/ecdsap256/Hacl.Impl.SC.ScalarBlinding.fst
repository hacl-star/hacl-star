module Hacl.Impl.SC.ScalarBlinding


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel
open Spec.P256.Definitions

open Spec.ECDSAP256.Definition

open FStar.Mul


assume val orderMultiplicationGeneral: a: felem -> b: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      wide_as_nat h1 out = as_nat h0 a * as_nat h0 b
    )


assume val orderMultiplicationECDSAP256Order: a: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      wide_as_nat h1 out = as_nat h0 a * prime_p256_order)


assume val blindingFactorAddition: a: felem -> k: felem -> out: widefelem -> 
  Stack unit 
    (requires fun h -> live h a /\ live h k /\ live h out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat h1 out = as_nat h0 a + as_nat h0 k * prime_p256_order /\
      as_nat h0 a == (wide_as_nat h1 out) % prime_p256_order)

