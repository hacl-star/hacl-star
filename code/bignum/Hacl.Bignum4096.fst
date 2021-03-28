module Hacl.Bignum4096

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module AM = Hacl.Bignum.AlmostMontgomery
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
  BN.bn_karatsuba_mul n_limbs a
  //BN.bn_mul n_limbs n_limbs a

let sqr (a:lbignum t_limbs n_limbs) : BN.bn_karatsuba_sqr_st t_limbs n_limbs a =
  BN.bn_karatsuba_sqr n_limbs a
  //BN.bn_sqr n_limbs a
  //BN.bn_mul n_limbs n_limbs a a

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

[@CInline]
let areduction: AM.bn_almost_mont_reduction_st t_limbs n_limbs =
  AM.bn_almost_mont_reduction bn_inst

[@CInline]
let amont_mul: AM.bn_almost_mont_mul_st t_limbs n_limbs =
  AM.bn_almost_mont_mul bn_inst areduction

[@CInline]
let amont_sqr: AM.bn_almost_mont_sqr_st t_limbs n_limbs =
  AM.bn_almost_mont_sqr bn_inst areduction

inline_for_extraction noextract
instance almost_mont_inst: AM.almost_mont t_limbs = {
  AM.bn = bn_inst;
  AM.mont_check;
  AM.precomp;
  AM.reduction = areduction;
  AM.to;
  AM.from;
  AM.mul = amont_mul;
  AM.sqr = amont_sqr;
}

[@CInline]
let bn_slow_precomp : BR.bn_mod_slow_precomp_st t_limbs n_limbs =
  BR.bn_mod_slow_precomp almost_mont_inst

let mod n a res =
  BS.mk_bn_mod_slow_safe n_limbs (BR.mk_bn_mod_slow almost_mont_inst bn_slow_precomp) n a res

let exp_check: BE.bn_check_mod_exp_st t_limbs n_limbs =
  BE.bn_check_mod_exp n_limbs

[@CInline]
let exp_vartime_precomp: BE.bn_mod_exp_precomp_st t_limbs n_limbs =
  BE.bn_mod_exp_vartime_precomp n_limbs
    (BE.bn_mod_exp_bm_vartime_precomp mont_inst)
    (BE.bn_mod_exp_fw_vartime_precomp mont_inst 4ul)

[@CInline]
let exp_consttime_precomp: BE.bn_mod_exp_precomp_st t_limbs n_limbs =
  BE.bn_mod_exp_consttime_precomp n_limbs
    (BE.bn_mod_exp_bm_consttime_precomp mont_inst)
    (BE.bn_mod_exp_fw_consttime_precomp mont_inst 4ul)

[@CInline]
let exp_vartime: BE.bn_mod_exp_st t_limbs n_limbs =
  BE.mk_bn_mod_exp n_limbs precomp exp_vartime_precomp

[@CInline]
let exp_consttime: BE.bn_mod_exp_st t_limbs n_limbs =
  BE.mk_bn_mod_exp n_limbs precomp exp_consttime_precomp

let mod_exp_vartime = BS.mk_bn_mod_exp_safe n_limbs exp_check exp_vartime

let mod_exp_consttime = BS.mk_bn_mod_exp_safe n_limbs exp_check exp_consttime

let mod_inv_prime_vartime = BS.mk_bn_mod_inv_prime_safe n_limbs exp_vartime

let mont_ctx_init r n =
  MA.bn_field_init mont_inst r n

let mont_ctx_free k =
  MA.bn_field_free k

let mod_precomp k a res =
  BS.bn_mod_ctx n_limbs bn_slow_precomp k a res

let mod_exp_vartime_precomp k a bBits b res =
  BS.mk_bn_mod_exp_ctx n_limbs exp_vartime_precomp k a bBits b res

let mod_exp_consttime_precomp k a bBits b res =
  BS.mk_bn_mod_exp_ctx n_limbs exp_consttime_precomp k a bBits b res

let mod_inv_prime_vartime_precomp k a res =
  BS.mk_bn_mod_inv_prime_ctx n_limbs
    (BI.mk_bn_mod_inv_prime_precomp n_limbs exp_vartime_precomp) k a res

let new_bn_from_bytes_be = BS.new_bn_from_bytes_be

let new_bn_from_bytes_le = BS.new_bn_from_bytes_le

let bn_to_bytes_be = Hacl.Bignum.Convert.mk_bn_to_bytes_be n_bytes

let bn_to_bytes_le = Hacl.Bignum.Convert.mk_bn_to_bytes_le n_bytes

let lt_mask = BN.bn_lt_mask n_limbs
