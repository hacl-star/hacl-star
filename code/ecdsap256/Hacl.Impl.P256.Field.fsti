module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let fmont_as_nat #l (h:mem) (a:felem l) = SM.from_mont (as_nat h a)


///  Create zero and one

val make_fzero: #l:limb_t -> n:felem l -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    fmont_as_nat h1 n == 0)


val make_fone: #l:limb_t -> n:felem l -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    fmont_as_nat h1 n == 1)


///  Comparison

val felem_is_lt_prime_mask: #l:limb_t -> f:felem l -> Stack (limb l)
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.prime then v r = ones_v U64 else v r = 0))


val feq_mask: #l:limb_t -> a:felem l -> b:felem l -> Stack (limb l)
  (requires fun h ->
    live h a /\ live h b /\ eq_or_disjoint a b /\
    as_nat h a < S.prime /\ as_nat h b < S.prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if fmont_as_nat h0 a = fmont_as_nat h0 b then v r == ones_v U64 else v r = 0))


///  Field Arithmetic

val fadd: #l:limb_t -> res:felem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fadd (as_nat h0 x) (as_nat h0 y) /\
    fmont_as_nat h1 res == S.fadd (fmont_as_nat h0 x) (fmont_as_nat h0 y))


inline_for_extraction noextract
val fdouble: #l:limb_t -> res:felem l -> x:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (2 * as_nat h0 x) % S.prime /\
    fmont_as_nat h1 res == (2 * fmont_as_nat h0 x) % S.prime)


val fsub: #l:limb_t -> res:felem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ live h y /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fsub (as_nat h0 x) (as_nat h0 y) /\
    fmont_as_nat h1 res == S.fsub (fmont_as_nat h0 x) (fmont_as_nat h0 y))


val fnegate_conditional_vartime: #l:limb_t -> f:felem l -> is_negate:bool -> Stack unit
  (requires fun h -> live h f /\ as_nat h f < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\ as_nat h1 f < S.prime /\
    as_nat h1 f == (if is_negate then (S.prime - as_nat h0 f) % S.prime else as_nat h0 f))


val fmul: #l:limb_t -> res:felem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 y * SM.fmont_R_inv) % S.prime /\
    fmont_as_nat h1 res = S.fmul (fmont_as_nat h0 x) (fmont_as_nat h0 y))


val fsqr: #l:limb_t -> res:felem l -> x:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 x * SM.fmont_R_inv) % S.prime /\
    fmont_as_nat h1 res = S.fmul (fmont_as_nat h0 x) (fmont_as_nat h0 x))


val from_mont: #l:limb_t -> res:felem l -> x:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ as_nat h x < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * SM.fmont_R_inv) % S.prime /\
    as_nat h1 res = fmont_as_nat h0 x)


val to_mont: #l:limb_t -> res:felem l -> f:felem l -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ eq_or_disjoint f res /\
    as_nat h f < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = SM.to_mont (as_nat h0 f))


///  Special cases of the above functions

val fmul_by_b_coeff: #l:limb_t -> res:felem l -> x:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res =
      S.fmul S.b_coeff (fmont_as_nat h0 x))


val fcube: #l:limb_t -> res:felem l  -> x:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res =
      S.fmul (S.fmul (fmont_as_nat h0 x) (fmont_as_nat h0 x)) (fmont_as_nat h0 x))
