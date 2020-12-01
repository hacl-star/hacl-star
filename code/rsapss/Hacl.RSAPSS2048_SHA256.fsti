module Hacl.RSAPSS2048_SHA256

open FStar.Mul
open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module RI = Hacl.Impl.RSAPSS
module RK = Hacl.Impl.RSAPSS.Keys
module BE = Hacl.Bignum.Exponentiation
module BP = Hacl.Bignum.ExponentiationPrecomp

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let n_limbs = 32ul // 2048/64

inline_for_extraction noextract
let modBits = 2048ul

inline_for_extraction noextract
let a_hash = Hash.SHA2_256

//a specialized version of bignum
inline_for_extraction noextract
val ke_2048: BP.exp t_limbs


val rsapss_sign: RI.rsapss_sign_st t_limbs ke_2048 a_hash modBits

val rsapss_verify: RI.rsapss_verify_st t_limbs ke_2048 a_hash modBits

val new_rsapss_load_pkey: RK.new_rsapss_load_pkey_st t_limbs ke_2048 modBits

val new_rsapss_load_skey: RK.new_rsapss_load_skey_st t_limbs ke_2048 modBits

val rsapss_skey_sign: RI.rsapss_skey_sign_st t_limbs ke_2048 a_hash modBits

val rsapss_pkey_verify: RI.rsapss_pkey_verify_st t_limbs ke_2048 a_hash modBits
