module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val fmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.prime)


// NOTE: changed precondition `eq_or_disjoint x y`
val fadd: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 x /\ live h0 y /\ live h0 res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h0 x < S.prime /\ as_nat h0 y < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime /\
    as_nat h1 res == SM.toDomain_ ((SM.fromDomain_ (as_nat h0 x) + SM.fromDomain_ (as_nat h0 y)) % S.prime))


inline_for_extraction noextract
val fdouble: x:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 x /\ live h0 res /\ eq_or_disjoint x res /\
    as_nat h0 x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (2 * as_nat h0 x) % S.prime /\
    as_nat h1 res < S.prime /\
    as_nat h1 res == SM.toDomain_ (2 * SM.fromDomain_ (as_nat h0 x) % S.prime))


// NOTE: changed precondition `eq_or_disjoint x y`
val fsub: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h0 ->
    live h0 res /\ live h0 x /\ live h0 y /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h0 x < S.prime /\ as_nat h0 y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime /\
    as_nat h1 res == SM.toDomain_ ((SM.fromDomain_ (as_nat h0 x) - SM.fromDomain_ (as_nat h0 y)) % S.prime))


// TODO: rename
val fromDomain: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * SM.mont_R_inv) % S.prime /\
    as_nat h1 res = SM.fromDomain_ (as_nat h0 a))


val fmul: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\
    as_nat h a < S.prime /\ as_nat h b < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * SM.mont_R_inv) % S.prime /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 b) % S.prime) /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 b)))


val fsqr: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 a * SM.mont_R_inv) % S.prime /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a)))


///  Special cases of the above functions

val fcube: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res = SM.toDomain_ (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a)))


inline_for_extraction noextract
val fmul_by_2: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == SM.toDomain_ (2 * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res == SM.toDomain_ (2 * SM.fromDomain_ (as_nat h0 a)) /\
    as_nat h1 res < S.prime)


val fmul_by_3: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res == SM.toDomain_ (3 * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res == SM.toDomain_ (3 * SM.fromDomain_ (as_nat h0 a)))


val fmul_by_4: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res == SM.toDomain_ (4 * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res == SM.toDomain_ (4 * SM.fromDomain_ (as_nat h0 a)))


val fmul_by_8: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res == SM.toDomain_ (8 * SM.fromDomain_ (as_nat h0 a) % S.prime) /\
    as_nat h1 res == SM.toDomain_ (8 * SM.fromDomain_ (as_nat h0 a)))
