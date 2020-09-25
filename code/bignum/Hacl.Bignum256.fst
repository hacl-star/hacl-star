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


let add = Hacl.Bignum.Addition.bn_add_eq_len n_limbs

let sub = Hacl.Bignum.Addition.bn_sub_eq_len n_limbs

let mul (a b: lbignum t_limbs n_limbs): BN.bn_karatsuba_mul_st a b =
  BN.bn_mul n_limbs a n_limbs b

let bit_set: BN.bn_set_ith_bit_st t_limbs n_limbs =
  BN.bn_set_ith_bit n_limbs

let add_mod_n: BN.bn_add_mod_n_st t_limbs n_limbs =
  BN.bn_add_mod_n n_limbs

let sub_mask: BN.bn_sub_mask_st t_limbs n_limbs =
  BN.bn_sub_mask n_limbs

let sqr (a: lbignum t_limbs n_limbs): BN.bn_karatsuba_sqr_st a =
  //BN.bn_sqr n_limbs a
  BN.bn_mul n_limbs a n_limbs a

inline_for_extraction noextract
instance bn_inst: BN.bn t_limbs n_limbs = {
  BN.bit_set;
  BN.add_mod_n;
  BN.mul;
  BN.sqr;
  BN.sub_mask
}

let check : BM.check_modulus_st t_limbs n_limbs =
  BM.check_modulus #t_limbs #n_limbs #bn_inst

let precomp: BM.precomp_r2_mod_n_st t_limbs n_limbs =
  BM.precomp_r2_mod_n #t_limbs #n_limbs #bn_inst

let reduction: BM.mont_reduction_st t_limbs n_limbs =
  BM.mont_reduction n_limbs

let to: BM.to_mont_st t_limbs n_limbs =
  BM.to_mont #t_limbs #n_limbs #bn_inst reduction

let from: BM.from_mont_st t_limbs n_limbs =
  BM.from_mont #t_limbs #n_limbs reduction

let mont_mul: BM.mont_mul_st t_limbs n_limbs =
  BM.mont_mul #t_limbs #n_limbs #bn_inst reduction

let mont_sqr: BM.mont_sqr_st t_limbs n_limbs =
  BM.mont_sqr #t_limbs #n_limbs #bn_inst reduction

inline_for_extraction noextract
instance mont_inst: BM.mont t_limbs n_limbs = {
  BM.bn = FStar.Tactics.Typeclasses.solve;
  BM.check;
  BM.precomp;
  BM.reduction;
  BM.to;
  BM.from;
  BM.mul = mont_mul;
  BM.sqr = mont_sqr;
}

let mod_precompr2 = BR.mk_bn_mod_slow_precompr2 n_limbs #mont_inst

let mod = BR.mk_bn_mod_slow n_limbs #mont_inst

let mod_exp_loop: BE.bn_mod_exp_loop_st t_limbs n_limbs =
  BE.bn_mod_exp_loop n_limbs #mont_inst

let mod_exp_precompr2 =
  BE.mk_bn_mod_exp_precompr2 n_limbs #mont_inst mod_exp_loop

let mod_exp =
  BE.mk_bn_mod_exp n_limbs #mont_inst mod_exp_loop

let mod_exp_mont_ladder_loop: BE.bn_mod_exp_mont_ladder_loop_st t_limbs n_limbs =
  BE.bn_mod_exp_mont_ladder_loop n_limbs #mont_inst

let mod_exp_mont_ladder_precompr2 =
  BE.mk_bn_mod_exp_mont_ladder_precompr2 n_limbs #mont_inst mod_exp_mont_ladder_loop

let mod_exp_mont_ladder =
  BE.mk_bn_mod_exp_mont_ladder n_limbs #mont_inst mod_exp_mont_ladder_loop

let new_precompr2 = BM.new_precomp_r2_mod_n

let mod_inv_prime = BI.mk_bn_mod_inv_prime n_limbs mod_exp

let new_bn_from_bytes_be = Hacl.Bignum.Convert.new_bn_from_bytes_be

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n_bytes

let lt_mask = Hacl.Bignum.mk_bn_lt_mask n_limbs
