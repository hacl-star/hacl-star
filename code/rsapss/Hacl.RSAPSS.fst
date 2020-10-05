module Hacl.RSAPSS

open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module RI = Hacl.Impl.RSAPSS
module RK = Hacl.Impl.RSAPSS.Keys

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

private
[@CInline]
let load_pkey : RK.rsapss_load_pkey_st t_limbs =
  RK.rsapss_load_pkey RK.mk_runtime_rsapss_checks

private
[@CInline]
let load_skey : RK.rsapss_load_skey_st t_limbs =
  RK.rsapss_load_skey RK.mk_runtime_rsapss_checks load_pkey


val rsapss_sign: len:BN.meta_len t_limbs -> RI.rsapss_sign_st t_limbs (BE.mk_runtime_exp len).BE.mont.BM.bn.BN.len
let rsapss_sign len a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  RI.rsapss_sign (BE.mk_runtime_exp len) a modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify: len:BN.meta_len t_limbs -> RI.rsapss_verify_st t_limbs (BE.mk_runtime_exp len).BE.mont.BM.bn.BN.len
let rsapss_verify len a modBits eBits pkey sLen k sgnt msgLen msg =
  RI.rsapss_verify (BE.mk_runtime_exp len) a modBits eBits pkey sLen k sgnt msgLen msg


val new_rsapss_load_pkey: RK.new_rsapss_load_pkey_st t_limbs
let new_rsapss_load_pkey r modBits eBits nb eb =
  RK.new_rsapss_load_pkey load_pkey r modBits eBits nb eb


val new_rsapss_load_skey: RK.new_rsapss_load_skey_st t_limbs
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  RK.new_rsapss_load_skey load_skey r modBits eBits dBits nb eb db


val rsapss_skey_sign: len:BN.meta_len t_limbs -> RI.rsapss_skey_sign_st t_limbs (BE.mk_runtime_exp len).BE.mont.BM.bn.BN.len
let rsapss_skey_sign len a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  RI.rsapss_skey_sign
    (BE.mk_runtime_exp len)
    load_skey
    (rsapss_sign len)
    a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt


val rsapss_pkey_verify: len:BN.meta_len t_limbs -> RI.rsapss_pkey_verify_st t_limbs (BE.mk_runtime_exp len).BE.mont.BM.bn.BN.len
let rsapss_pkey_verify len a modBits eBits nb eb sLen k sgnt msgLen msg =
  RI.rsapss_pkey_verify
    (BE.mk_runtime_exp len)
    load_pkey
    (rsapss_verify len)
     a modBits eBits nb eb sLen k sgnt msgLen msg
