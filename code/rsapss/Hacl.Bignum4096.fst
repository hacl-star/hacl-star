module Hacl.Bignum4096

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation

friend Hacl.Bignum.Exponentiation

let _ = assert_norm (4096ul = 64ul `FStar.UInt32.mul` 64ul)

inline_for_extraction noextract
let n': BN.meta_len = 65ul

/// A note about the style of normalization used in this file. Normally,
/// bn_sub_eq_len and others would be marked as inline_for_extraction. However,
/// we want to keep a copy of the functions that take the nLen parameter at
/// runtime, meaning we can't blindly mark everything as inline_for_extraction,
/// otherwise the copy of the code that a runtime-parametric over the length
/// would be horrendous. So instead we do the inline_by_extraction "by hand" via
/// a call to `norm`. Note that these are all partial applications, meaning that
/// we normalize pure terms.


let add = Hacl.Bignum.Addition.bn_add_eq_len n

let sub = Hacl.Bignum.Addition.bn_sub_eq_len n

let mul (a b: lbignum n): BN.bn_mul_st a b =
  BN.bn_mul n a n b

let bit_set: BN.bn_bit_set_st n =
  BN.(norm [ zeta; primops; iota; delta_only [ `%bn_bit_set ] ] (bn_bit_set n))

let add_mod_n: BN.bn_add_mod_n_st n =
  BN.bn_add_mod_n n

let sub_mask: BN.bn_sub_mask_st n =
  BN.bn_sub_mask n

let mul' (a b: lbignum n'): BN.bn_mul_st a b =
  BN.bn_mul n' a n' b

inline_for_extraction noextract
instance bn_inst: BN.bn n = {
  BN.bit_set;
  BN.add_mod_n;
  BN.mul;
  BN.mul';
  BN.sub_mask
}

let precomp: BM.precomp_r2_mod_n_st n =
  BM.precomp_r2_mod_n #n #bn_inst

let reduction: BM.mont_reduction_st n =
  BM.mont_reduction n

let to: BM.to_mont_st n =
  BM.to_mont #n #bn_inst reduction

let from: BM.from_mont_st n =
  BM.from_mont #n reduction

let mont_mul: BM.mont_mul_st n =
  BM.mont_mul #n #bn_inst reduction

inline_for_extraction noextract
instance mont_inst: BM.mont n = {
  BM.bn = FStar.Tactics.Typeclasses.solve;
  BM.precomp;
  BM.reduction;
  BM.to;
  BM.from;
  BM.mul = mont_mul;
}

let mod_exp_loop: BE.bn_mod_exp_loop_st n =
  norm [ zeta; primops; iota; delta_only [ `%BE.bn_mod_exp_loop ] ] (BE.bn_mod_exp_loop n #mont_inst)

let mod_exp =
  BE.mk_bn_mod_exp 4096ul n #mont_inst mod_exp_loop

let new_bn_from_bytes_be = Hacl.Bignum.Convert.new_bn_from_bytes_be

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n

let lt = Hacl.Bignum.mk_bn_is_less n
