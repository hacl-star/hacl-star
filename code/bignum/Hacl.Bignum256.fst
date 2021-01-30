module Hacl.Bignum256

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BI = Hacl.Bignum.ModInv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let add: BN.bn_add_eq_len_st t_limbs n_limbs =
  BN.bn_add_eq_len n_limbs

let sub: BN.bn_sub_eq_len_st t_limbs n_limbs =
  BN.bn_sub_eq_len n_limbs

[@CInline]
let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
  BN.bn_add_mod_n n_limbs

let mul (a:lbignum t_limbs n_limbs) : BN.bn_karatsuba_mul_st t_limbs n_limbs a =
  BN.bn_mul n_limbs n_limbs a

[@CInline]
let sqr (a:lbignum t_limbs n_limbs) : BN.bn_karatsuba_sqr_st t_limbs n_limbs a =
  //BN.bn_sqr n_limbs a
  BN.bn_mul n_limbs n_limbs a a

inline_for_extraction noextract
instance bn_inst: BN.bn t_limbs = {
  BN.len = n_limbs;
  BN.add;
  BN.sub;
  BN.add_mod_n;
  BN.mul;
  BN.sqr
}

[@CInline]
let mont_check: BM.bn_check_modulus_st t_limbs n_limbs =
  BM.bn_check_modulus

[@CInline]
let precomp: BM.bn_precomp_r2_mod_n_st t_limbs n_limbs =
  BM.bn_precomp_r2_mod_n bn_inst

[@CInline]
let reduction: BM.bn_mont_reduction_st t_limbs n_limbs =
  BM.bn_mont_reduction bn_inst

[@CInline]
let to: BM.bn_to_mont_st t_limbs n_limbs =
  BM.bn_to_mont bn_inst reduction

[@CInline]
let from: BM.bn_from_mont_st t_limbs n_limbs =
  BM.bn_from_mont bn_inst reduction

[@CInline]
let mont_mul: BM.bn_mont_mul_st t_limbs n_limbs =
  BM.bn_mont_mul bn_inst reduction

[@CInline]
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

let mod_precompr2 = BR.bn_mod_slow_precompr2 mont_inst

let mod = BS.bn_mod_slow_safe mont_inst mod_precompr2

[@CInline]
let exp_check: BE.bn_check_mod_exp_st t_limbs n_limbs =
  BE.bn_check_mod_exp mont_inst

let mod_exp_raw_precompr2: BE.bn_mod_exp_raw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_raw_precompr2 mont_inst

let mod_exp_ct_precompr2: BE.bn_mod_exp_ct_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_ct_precompr2 mont_inst

[@CInline]
let mod_exp_fw_raw_precompr2: BE.bn_mod_exp_fw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_fw_raw_precompr2 mont_inst

[@CInline]
let mod_exp_fw_ct_precompr2: BE.bn_mod_exp_fw_precompr2_st t_limbs n_limbs =
  BE.bn_mod_exp_fw_ct_precompr2 mont_inst

inline_for_extraction noextract
instance exp_inst: BE.exp t_limbs = {
  BE.mont = mont_inst;
  BE.exp_check;
  BE.raw_mod_exp_precomp = mod_exp_raw_precompr2;
  BE.ct_mod_exp_precomp = mod_exp_ct_precompr2;
  BE.raw_mod_exp_fw_precomp = mod_exp_fw_raw_precompr2;
  BE.ct_mod_exp_fw_precomp = mod_exp_fw_ct_precompr2;
}

let mod_exp_raw = BS.bn_mod_exp_raw_safe exp_inst

let mod_exp_ct = BS.bn_mod_exp_ct_safe exp_inst

let new_precompr2 = BS.new_bn_precomp_r2_mod_n mont_inst

let mod_inv_prime_raw = BS.bn_mod_inv_prime_raw_safe exp_inst

let new_bn_from_bytes_be = BS.new_bn_from_bytes_be

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n_bytes

let lt_mask = BN.bn_lt_mask n_limbs
