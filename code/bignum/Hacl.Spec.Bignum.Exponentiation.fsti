module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// This function is *NOT* constant-time on the exponent b
val bn_mod_exp_precompr2:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64)
  -> r2:lbignum nLen ->
  lbignum nLen


val bn_mod_exp_precompr2_lemma:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64)
  -> r2:lbignum nLen -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (128 * nLen) % bn_v n)
  (ensures
    bn_v (bn_mod_exp_precompr2 nLen n a bBits b r2) == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b))


// This function is constant-time on the exponent b
val bn_mod_exp_mont_ladder_precompr2:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64)
  -> r2:lbignum nLen ->
  lbignum nLen


val bn_mod_exp_mont_ladder_precompr2_lemma:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64)
  -> r2:lbignum nLen -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (128 * nLen) % bn_v n)
  (ensures
    bn_v (bn_mod_exp_mont_ladder_precompr2 nLen n a bBits b r2) == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b))


// This function is *NOT* constant-time on the exponent b
val bn_mod_exp:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> nBits:size_pos
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  lbignum nLen


val bn_mod_exp_lemma:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> nBits:size_pos
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n)
  (ensures
    bn_v (bn_mod_exp nLen nBits n a bBits b) == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b))


// This function is constant-time on the exponent b
val bn_mod_exp_mont_ladder:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> nBits:size_pos
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  lbignum nLen


val bn_mod_exp_mont_ladder_lemma:
    nLen:size_pos{128 * nLen <= max_size_t}
  -> nBits:size_pos
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n)
  (ensures
    bn_v (bn_mod_exp_mont_ladder nLen nBits n a bBits b) == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b))
