module Hacl.Bignum256

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BI = Hacl.Bignum.ModInv

friend Hacl.Bignum.Exponentiation

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


let add (a b: lbignum t_limbs n_limbs) : BN.bn_add_eq_len_st a b =
  BN.bn_add_eq_len n_limbs a b

let sub (a b: lbignum t_limbs n_limbs) : BN.bn_sub_eq_len_st a b =
  BN.bn_sub_eq_len n_limbs a b

let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
 BN.bn_add_mod_n n_limbs

let mul (a b: lbignum t_limbs n_limbs): BN.bn_karatsuba_mul_st a b =
  BN.bn_mul n_limbs a n_limbs b

let sqr (a: lbignum t_limbs n_limbs): BN.bn_karatsuba_sqr_st a =
  //BN.bn_sqr n_limbs a
  BN.bn_mul n_limbs a n_limbs a

inline_for_extraction noextract
instance bn_inst: BN.bn = {
  BN.t = t_limbs;
  BN.len = n_limbs;
  BN.add;
  BN.sub;
  BN.add_mod_n;
  BN.mul;
  BN.sqr
}

let check : BM.bn_check_modulus_st t_limbs n_limbs =
  BM.bn_check_modulus bn_inst

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
instance mont_inst: BM.mont = {
  BM.bn = FStar.Tactics.Typeclasses.solve;
  BM.check;
  BM.precomp;
  BM.reduction;
  BM.to;
  BM.from;
  BM.mul = mont_mul;
  BM.sqr = mont_sqr;
}

let mod_precompr2 = BR.mk_bn_mod_slow_precompr2 mont_inst

let mod = BR.mk_bn_mod_slow mont_inst

let exp_check = BE.bn_check_mod_exp mont_inst

let mod_exp_precompr2 = BE.bn_mod_exp_precompr2 mont_inst

let mod_exp = BE.bn_mod_exp mont_inst

let mod_exp_mont_ladder_precompr2 = BE.bn_mod_exp_mont_ladder_precompr2 mont_inst

let mod_exp_mont_ladder = BE.bn_mod_exp_mont_ladder mont_inst

inline_for_extraction noextract
instance exp_inst: BE.exp = {
  BE.mont = FStar.Tactics.Typeclasses.solve;
  BE.exp_check;
  BE.mod_exp_precomp = mod_exp_precompr2;
  BE.ct_mod_exp_precomp = mod_exp_mont_ladder_precompr2;
  BE.mod_exp;
  BE.ct_mod_exp = mod_exp_mont_ladder;
}


let new_precompr2 = BM.new_bn_precomp_r2_mod_n

let mod_inv_prime = BI.mk_bn_mod_inv_prime exp_inst

let new_bn_from_bytes_be = Hacl.Bignum.Convert.new_bn_from_bytes_be

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n_bytes

let lt_mask = BN.mk_bn_lt_mask n_limbs
