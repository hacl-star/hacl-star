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

let fmont_as_nat (h:mem) (a:felem) = SM.fromDomain_ (as_nat h a)


val make_fzero: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.toDomain_ 0 /\
    SM.fromDomain_ (as_nat h1 n) == 0)


val make_fone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.toDomain_ 1 /\
    SM.fromDomain_ (as_nat h1 n) == 1)


val fmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.prime)


val is_felem_lt_prime_vartime: f:felem -> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == (as_nat h0 f < S.prime))


// NOTE: changed precondition `eq_or_disjoint x y`
val fadd: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fadd (as_nat h0 x) (as_nat h0 y) /\
    fmont_as_nat h1 res == S.fadd (fmont_as_nat h0 x) (fmont_as_nat h0 y))


inline_for_extraction noextract
val fdouble: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (2 * as_nat h0 x) % S.prime /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res == (2 * fmont_as_nat h0 x) % S.prime)


// NOTE: changed precondition `eq_or_disjoint x y`
val fsub: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ live h y /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fsub (as_nat h0 x) (as_nat h0 y) /\
    fmont_as_nat h1 res == S.fsub (fmont_as_nat h0 x) (fmont_as_nat h0 y))


// TODO: rename
val fromDomain: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * SM.mont_R_inv) % S.prime /\
    as_nat h1 res = fmont_as_nat h0 a)


val fmul: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\
    as_nat h a < S.prime /\ as_nat h b < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * SM.mont_R_inv) % S.prime /\
    fmont_as_nat h1 res = S.fmul (fmont_as_nat h0 a) (fmont_as_nat h0 b))


val fsqr: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 a * SM.mont_R_inv) % S.prime /\
    fmont_as_nat h1 res = S.fmul (fmont_as_nat h0 a) (fmont_as_nat h0 a))


///  Special cases of the above functions

val fcube: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res =
      S.fmul (S.fmul (fmont_as_nat h0 a) (fmont_as_nat h0 a)) (fmont_as_nat h0 a))


val fmul_by_3: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res == (3 * fmont_as_nat h0 a) % S.prime)


val fmul_by_4: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res == (4 * fmont_as_nat h0 a) % S.prime)


val fmul_by_8: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res == (8 * fmont_as_nat h0 a) % S.prime)
