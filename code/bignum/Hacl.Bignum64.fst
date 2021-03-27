module Hacl.Bignum64

open FStar.Mul

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module AM = Hacl.Bignum.AlmostMontgomery
module MA = Hacl.Bignum.MontArithmetic
module BI = Hacl.Bignum.ModInv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let kam (len:BN.meta_len t_limbs) =
  AM.mk_runtime_almost_mont #t_limbs len

inline_for_extraction noextract
let ke (len:BN.meta_len t_limbs) =
  BE.mk_runtime_exp #t_limbs len

let add len a b res =
  (ke len).BE.bn.BN.add a b res

let sub len a b res =
  (ke len).BE.bn.BN.sub a b res

let mul len a b res =
  (ke len).BE.bn.BN.mul a b res

let sqr len a res =
  (ke len).BE.bn.BN.sqr a res

[@CInline]
let bn_slow_precomp (len:BN.meta_len t_limbs) : BR.bn_mod_slow_precomp_st t_limbs len =
  BR.bn_mod_slow_precomp (kam len)

let mod len n a res =
  BS.mk_bn_mod_slow_safe len (BR.mk_bn_mod_slow (kam len) (bn_slow_precomp len)) n a res

let mod_exp_vartime len n a bBits b res =
  BS.mk_bn_mod_exp_safe len (ke len).BE.exp_check (ke len).BE.exp_vt n a bBits b res

let mod_exp_consttime len n a bBits b res =
  BS.mk_bn_mod_exp_safe len (ke len).BE.exp_check (ke len).BE.exp_ct n a bBits b res

let mod_inv_prime_vartime len n a res =
  BS.mk_bn_mod_inv_prime_safe len (ke len).BE.exp_vt n a res

let mod_precomp k a res =
  BS.bn_mod_ctx k (bn_slow_precomp k.MA.len) a res

let mod_exp_vartime_precomp k a bBits b res =
  BS.mk_bn_mod_exp_ctx k (ke k.MA.len).BE.exp_vt_precomp a bBits b res

let mod_exp_consttime_precomp k a bBits b res =
  BS.mk_bn_mod_exp_ctx k (ke k.MA.len).BE.exp_ct_precomp a bBits b res

let mod_inv_prime_vartime_precomp k a res =
  BS.mk_bn_mod_inv_prime_ctx k (BI.mk_bn_mod_inv_prime_precomp k.MA.len (ke k.MA.len).BE.exp_vt_precomp) a res

let new_bn_from_bytes_be r len b =
  BS.new_bn_from_bytes_be r len b

let new_bn_from_bytes_le r len b =
  BS.new_bn_from_bytes_le r len b

let bn_to_bytes_be len b res =
  Hacl.Bignum.Convert.mk_bn_to_bytes_be len b res

let bn_to_bytes_le len b res =
  Hacl.Bignum.Convert.mk_bn_to_bytes_le len b res

let lt_mask len a b =
  BN.bn_lt_mask len a b
