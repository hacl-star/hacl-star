module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

include Hacl.Spec.Bignum.ExpBM
include Hacl.Spec.Bignum.ExpFW

module BM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mod_exp_raw #t nLen nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_raw_precompr2 nLen n a bBits b r2


let bn_mod_exp_raw_lemma #t nLen nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_raw_precompr2_lemma nLen n a bBits b r2


let bn_mod_exp_ct #t nLen nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_ct_precompr2 nLen n a bBits b r2


let bn_mod_exp_ct_lemma #t nLen nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_ct_precompr2_lemma nLen n a bBits b r2


let bn_mod_exp_fw #t nLen nBits n a bBits b l =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_fw_precompr2 #t nLen n a bBits b l r2


let bn_mod_exp_fw_lemma #t nLen nBits n a bBits b l =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_fw_precompr2_lemma #t nLen n a bBits b l r2
