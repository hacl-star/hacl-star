module Hacl.Impl.MM.Exponent


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Impl.LowLevel
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Ladder

open FStar.Mul

open Hacl.Impl.MontgomeryMultiplication
open Lib.Loops

#reset-options "--z3refresh --z3rlimit 200"

noextract
let prime = prime_p256_order



let order_inverse_buffer: x: ilbuffer uint8 32ul {witnessed x prime_p256_order_inverse_seq /\ recallable x} = 
  createL_global prime_p256_order_inverse_list

let order_buffer: x: ilbuffer uint8 32ul {witnessed x prime_p256_order_seq /\ recallable x} = 
  createL_global prime_p256_order_list 


val montgomery_ladder_exponent: a: felem -> Stack unit 
  (requires fun h -> live h a /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    (
      let b_ = fromDomain_ (as_nat h0 a) in 
      let r0D = exponent_spec b_ in 
      fromDomain_ (as_nat h1 a) == r0D  /\
      as_nat h1 a < prime
    )
)

val fromDomainImpl: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result == fromDomain_ (as_nat h0 a))

val multPower: a: felem -> b: felem ->  result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < prime /\ as_nat h b < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = (Hacl.Spec.P256.Definitions.pow (as_nat h0 a) (prime_p256_order - 2)  * (as_nat h0 b)) % prime_p256_order)


val multPowerPartial: a: felem -> b: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat h a < prime /\ as_nat h b < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1)
