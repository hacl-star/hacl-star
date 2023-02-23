module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 50"

val fmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % prime256)


// NOTE: changed precondition `eq_or_disjoint x y`
val fadd: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 x /\ live h0 y /\ live h0 res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h0 x < prime256 /\ as_nat h0 y < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % prime256 /\
    as_nat h1 res == toDomain_ ((fromDomain_ (as_nat h0 x) + fromDomain_ (as_nat h0 y)) % prime256))


inline_for_extraction noextract
val fdouble: x:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 x /\ live h0 res /\ eq_or_disjoint x res /\
    as_nat h0 x < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (2 * as_nat h0 x) % prime256 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res == toDomain_ (2 * fromDomain_ (as_nat h0 x) % prime256))


// NOTE: changed precondition `eq_or_disjoint x y`
val fsub: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 res /\ live h0 x /\ live h0 y /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h0 x < prime256 /\ as_nat h0 y < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x - as_nat h0 y) % prime256 /\
    as_nat h1 res == toDomain_ ((fromDomain_ (as_nat h0 x) - fromDomain_ (as_nat h0 y)) % prime256))


// TODO: rename
val montgomery_multiplication_buffer_by_one: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 res = fromDomain_ (as_nat h0 a))


val fmul: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\
    as_nat h a < prime256 /\ as_nat h b < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))


val fsqr: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))


///  Special cases of the above functions

val fcube: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))


inline_for_extraction noextract
val fmul_by_2: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == toDomain_ (2 * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res == toDomain_ (2 * fromDomain_ (as_nat h0 a)) /\
    as_nat h1 res < prime256)


val fmul_by_3: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res == toDomain_ (3 * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res == toDomain_ (3 * fromDomain_ (as_nat h0 a)))


val fmul_by_4: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res == toDomain_ (4 * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res == toDomain_ (4 * fromDomain_ (as_nat h0 a)))


val fmul_by_8: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < prime256 /\
    as_nat h1 res == toDomain_ (8 * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 res == toDomain_ (8 * fromDomain_ (as_nat h0 a)))
