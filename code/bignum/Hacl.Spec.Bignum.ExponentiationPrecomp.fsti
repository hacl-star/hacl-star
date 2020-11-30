module Hacl.Spec.Bignum.ExponentiationPrecomp

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BM = Hacl.Spec.Bignum.Montgomery
module BE = Hacl.Spec.Bignum.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


val bn_mod_exp_fw_precompr2:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l <= bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen ->
  lbignum t nLen


val bn_mod_exp_fw_precompr2_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l <= bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen -> Lemma
  (requires
    BE.bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
    BE.bn_mod_exp_post n a bBits b (bn_mod_exp_fw_precompr2 nLen n a bBits b l r2))


val bn_mod_exp_fw:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l <= bits t /\ pow2 l * nLen <= max_size_t} ->
  lbignum t nLen


val bn_mod_exp_fw_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l <= bits t /\ pow2 l * nLen <= max_size_t} -> Lemma
  (requires BE.bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  BE.bn_mod_exp_post n a bBits b (bn_mod_exp_fw nLen nBits n a bBits b l))
