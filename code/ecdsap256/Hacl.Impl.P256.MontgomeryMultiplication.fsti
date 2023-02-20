module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Constants
open Spec.P256.Lemmas
open Spec.P256.MontgomeryMultiplication

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Field

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val montgomery_multiplication_buffer_by_one: a:felem -> result:felem -> Stack unit
  (requires fun h -> live h a /\ as_nat h a < prime256 /\ live h result)
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = fromDomain_ (as_nat h0 a))


val montgomery_multiplication_buffer: a:felem -> b:felem -> result:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h result /\
    eq_or_disjoint a b /\
    as_nat h a < prime256 /\ as_nat h b < prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))


val montgomery_square_buffer: a:felem -> result:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h result /\ as_nat h a < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))


val exponent: a:felem -> result:felem -> tempBuffer:lbuffer uint64 (size 20) -> Stack unit
  (requires fun h ->
    live h a /\ live h tempBuffer /\ live h result /\
    disjoint tempBuffer result /\ disjoint a tempBuffer /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\
    as_nat h1 result = toDomain_ ((pow (fromDomain_ (as_nat h0 a)) (prime256 - 2)) % prime256))
