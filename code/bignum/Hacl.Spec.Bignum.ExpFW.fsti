module Hacl.Spec.Bignum.ExpFW

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BM = Hacl.Spec.Bignum.Montgomery
module EBM = Hacl.Spec.Bignum.ExpBM

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_mod_exp_fw_precompr2:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l < bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen ->
  lbignum t nLen


val bn_mod_exp_fw_precompr2_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l < bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen -> Lemma
  (requires
    EBM.bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
    EBM.bn_mod_exp_post n a bBits b (bn_mod_exp_fw_precompr2 nLen n a bBits b l r2))
