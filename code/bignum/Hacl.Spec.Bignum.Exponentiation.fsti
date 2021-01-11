module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
include Hacl.Spec.Bignum.ExpBM
include Hacl.Spec.Bignum.ExpFW

module BM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// This function is *NOT* constant-time on the exponent b
val bn_mod_exp:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) ->
  lbignum t nLen


val bn_mod_exp_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) -> Lemma
  (requires bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  bn_mod_exp_post n a bBits b (bn_mod_exp nLen nBits n a bBits b))


// This function is constant-time on the exponent b
val bn_mod_exp_mont_ladder:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) ->
  lbignum t nLen


val bn_mod_exp_mont_ladder_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) -> Lemma
  (requires bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  bn_mod_exp_post n a bBits b (bn_mod_exp_mont_ladder nLen nBits n a bBits b))


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
  (requires bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  bn_mod_exp_post n a bBits b (bn_mod_exp_fw nLen nBits n a bBits b l))
