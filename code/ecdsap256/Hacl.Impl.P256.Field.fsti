module Hacl.Impl.P256.Field // before: Hacl.Impl.P256.LowLevel.PrimeSpecific

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

#set-options "--z3rlimit 300"


let prime256_buffer: x: glbuffer uint64 4ul {
  witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\
  recallable x /\
  felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256} =

  assert_norm (felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction
val reduction_prime256_2prime256_8_with_carry_impl: x:widefelem -> result:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h result /\ eq_or_disjoint x result /\
    wide_as_nat h x < 2 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = wide_as_nat h0 x % prime256)


val reduction_prime_2prime_impl: x:felem -> result:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result == as_nat h0 x % prime256)


val p256_add: arg1:felem -> arg2:felem -> out:felem -> Stack unit
  (requires fun h0 ->
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime256 /\
    as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg2)) % prime256))


val p256_double: arg1:felem -> out:felem -> Stack unit
  (requires fun h0 ->
    live h0 arg1 /\ live h0 out /\ eq_or_disjoint arg1 out /\
    as_nat h0 arg1 < prime256)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == (2 * as_nat h0 arg1) % prime256 /\
    as_nat h1 out < prime256 /\
    as_nat h1 out == toDomain_ (2 * fromDomain_ (as_nat h0 arg1) % prime256))


val p256_sub: arg1:felem -> arg2:felem -> out:felem -> Stack unit
  (requires fun h0 ->
    live h0 out /\ live h0 arg1 /\ live h0 arg2 /\
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256 /\
    as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) - fromDomain_ (as_nat h0 arg2)) % prime256))


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
