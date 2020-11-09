module Hacl.FFDHE4096

open Lib.IntTypes

module S = Spec.FFDHE
module DH = Hacl.Impl.FFDHE
module BD = Hacl.Bignum.Definitions
module BE = Hacl.Bignum.Exponentiation

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let add (a b: BD.lbignum t_limbs n_limbs): BN.bn_add_eq_len_st a b =
  BN.bn_add_eq_len n_limbs a b

let sub (a b: BD.lbignum t_limbs n_limbs): BN.bn_sub_eq_len_st a b =
  BN.bn_sub_eq_len n_limbs a b

let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
 BN.bn_add_mod_n n_limbs

let mul (a b: BD.lbignum t_limbs n_limbs): BN.bn_karatsuba_mul_st a b =
  BN.bn_mul n_limbs a n_limbs b

let sqr (a: BD.lbignum t_limbs n_limbs): BN.bn_karatsuba_sqr_st a =
  //BN.bn_sqr n_limbs a
  BN.bn_mul n_limbs a n_limbs a

inline_for_extraction noextract
instance bn_inst: BN.bn t_limbs = {
  BN.len = n_limbs;
  BN.add;
  BN.sub;
  BN.add_mod_n;
  BN.mul;
  BN.sqr
}


let mont_check : BM.bn_check_modulus_st t_limbs n_limbs =
  BM.bn_check_modulus

let precomp: BM.bn_precomp_r2_mod_n_st t_limbs n_limbs =
  BM.bn_precomp_r2_mod_n bn_inst

let reduction: BM.bn_mont_reduction_st t_limbs n_limbs =
  BM.bn_mont_reduction bn_inst

let to: BM.bn_to_mont_st t_limbs n_limbs =
  BM.bn_to_mont bn_inst reduction

let from: BM.bn_from_mont_st t_limbs n_limbs =
  BM.bn_from_mont bn_inst reduction

let mont_mul: BM.bn_mont_mul_st t_limbs n_limbs =
  BM.bn_mont_mul bn_inst reduction

let mont_sqr: BM.bn_mont_sqr_st t_limbs n_limbs =
  BM.bn_mont_sqr bn_inst reduction

inline_for_extraction noextract
instance mont_inst: BM.mont t_limbs = {
  BM.bn = bn_inst;
  BM.mont_check;
  BM.precomp;
  BM.reduction;
  BM.to;
  BM.from;
  BM.mul = mont_mul;
  BM.sqr = mont_sqr;
}


let exp_check: BE.bn_check_mod_exp_st t_limbs n_limbs =
  BE.bn_check_mod_exp mont_inst

let mod_exp_precompr2: BE.bn_mod_exp_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_precompr2 mont_inst

let mod_exp: BE.bn_mod_exp_st t_limbs n_limbs =
  BE.bn_mod_exp mont_inst mod_exp_precompr2

let mod_exp_mont_ladder_precompr2: BE.bn_mod_exp_mont_ladder_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_mont_ladder_precompr2 mont_inst

let mod_exp_mont_ladder: BE.bn_mod_exp_mont_ladder_st t_limbs n_limbs =
  BE.bn_mod_exp_mont_ladder mont_inst mod_exp_mont_ladder_precompr2

inline_for_extraction noextract
instance ke_4096: BE.exp t_limbs = {
  BE.mont = mont_inst;
  BE.exp_check;
  BE.mod_exp_precomp = mod_exp_precompr2;
  BE.ct_mod_exp_precomp = mod_exp_mont_ladder_precompr2;
  BE.mod_exp = mod_exp;
  BE.ct_mod_exp = mod_exp_mont_ladder;
}


private
[@CInline]
let ffdhe_check_pk : DH.ffdhe_check_pk_st t_limbs a_ffdhe len =
  DH.ffdhe_check_pk #t_limbs a_ffdhe len

private
[@CInline]
let ffdhe_compute_exp : DH.ffdhe_compute_exp_st t_limbs a_ffdhe len ke_4096 =
  DH.ffdhe_compute_exp a_ffdhe len ke_4096


let ffdhe_secret_to_public sk pk =
  DH.ffdhe_secret_to_public a_ffdhe len ke_4096 ffdhe_compute_exp sk pk


let ffdhe_shared_secret sk pk ss =
  DH.ffdhe_shared_secret a_ffdhe len ke_4096 ffdhe_check_pk ffdhe_compute_exp sk pk ss
