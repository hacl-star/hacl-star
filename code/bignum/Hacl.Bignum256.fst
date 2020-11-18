module Hacl.Bignum256

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BI = Hacl.Bignum.ModInv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let _ = assert_norm (256ul = 64ul `FStar.UInt32.mul` 4ul)

/// A note about the style of normalization used in this file. Normally,
/// bn_sub_eq_len and others would be marked as inline_for_extraction. However,
/// we want to keep a copy of the functions that take the nLen parameter at
/// runtime, meaning we can't blindly mark everything as inline_for_extraction,
/// otherwise the copy of the code that a runtime-parametric over the length
/// would be horrendous. So instead we do the inline_by_extraction "by hand" via
/// a call to `norm`. Note that these are all partial applications, meaning that
/// we normalize pure terms.


let add: BN.bn_add_eq_len_st t_limbs n_limbs =
  BN.bn_add_eq_len n_limbs

let sub: BN.bn_sub_eq_len_st t_limbs n_limbs =
  BN.bn_sub_eq_len n_limbs

let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
  BN.bn_add_mod_n n_limbs

let mul (a:lbignum t_limbs n_limbs) : BN.bn_karatsuba_mul_st t_limbs n_limbs a =
  BN.bn_mul n_limbs n_limbs a

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

let mont_check: BM.bn_check_modulus_st t_limbs n_limbs =
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

let mod_precompr2 = BR.bn_mod_slow_precompr2 mont_inst

let mod_check : BR.bn_check_bn_mod_st t_limbs n_limbs =
  BR.bn_check_bn_mod mont_inst

let mod' : BR.bn_mod_slow_st t_limbs n_limbs = BR.bn_mod_slow mont_inst mod_precompr2

let mod = BS.bn_mod_slow_safe mont_inst mod_check mod'

let exp_check = BE.bn_check_mod_exp mont_inst

let mod_exp_precompr2 = BE.bn_mod_exp_precompr2 mont_inst

let mod_exp' : BE.bn_mod_exp_st t_limbs n_limbs =
  BE.bn_mod_exp mont_inst mod_exp_precompr2

let mod_exp = BS.bn_mod_exp_safe mont_inst exp_check mod_exp'

let mod_exp_mont_ladder_precompr2 = BE.bn_mod_exp_mont_ladder_precompr2 mont_inst

let mod_exp_mont_ladder' : BE.bn_mod_exp_mont_ladder_st t_limbs n_limbs =
  BE.bn_mod_exp_mont_ladder mont_inst mod_exp_mont_ladder_precompr2

let mod_exp_mont_ladder = BS.bn_mod_exp_mont_ladder_safe mont_inst exp_check mod_exp_mont_ladder'

inline_for_extraction noextract
instance exp_inst: BE.exp t_limbs = {
  BE.mont = mont_inst;
  BE.exp_check;
  BE.mod_exp_precomp = mod_exp_precompr2;
  BE.ct_mod_exp_precomp = mod_exp_mont_ladder_precompr2;
  BE.mod_exp = mod_exp';
  BE.ct_mod_exp = mod_exp_mont_ladder';
}

let new_precompr2 = BS.new_bn_precomp_r2_mod_n mont_inst

let mod_inv_prime = BS.bn_mod_inv_prime_safe exp_inst

let new_bn_from_bytes_be = BS.new_bn_from_bytes_be

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n_bytes

let lt_mask = BN.bn_lt_mask n_limbs
