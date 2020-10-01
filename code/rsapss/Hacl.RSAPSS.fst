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

val rsapss_sign: len:BN.meta_len U64 -> RI.rsapss_sign_st U64 (BE.mk_runtime_exp_uint64 len).BE.mont.BM.bn.BN.len
let rsapss_sign len a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  RI.rsapss_sign (BE.mk_runtime_exp_uint64 len) a modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify: len:BN.meta_len U64 -> RI.rsapss_verify_st U64 (BE.mk_runtime_exp_uint64 len).BE.mont.BM.bn.BN.len
let rsapss_verify len a modBits eBits pkey sLen k sgnt msgLen msg =
  RI.rsapss_verify (BE.mk_runtime_exp_uint64 len) a modBits eBits pkey sLen k sgnt msgLen msg


val new_rsapss_load_pkey: RK.new_rsapss_load_pkey_st U64
let new_rsapss_load_pkey r modBits eBits nb eb =
  RK.new_rsapss_load_pkey RK.load_pkey_u64 r modBits eBits nb eb


val new_rsapss_load_skey: RK.new_rsapss_load_skey_st U64
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  RK.new_rsapss_load_skey RK.mk_runtime_rsapss_load_keys_uint64 r modBits eBits dBits nb eb db


val rsapss_skey_sign: len:BN.meta_len U64 -> RI.rsapss_skey_sign_st U64 (BE.mk_runtime_exp_uint64 len).BE.mont.BM.bn.BN.len
let rsapss_skey_sign len a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  RI.rsapss_skey_sign
    (BE.mk_runtime_exp_uint64 len)
     RK.mk_runtime_rsapss_load_keys_uint64
    (RI.mk_runtime_rsapss_uint64 len)
    a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt


val rsapss_pkey_verify: len:BN.meta_len U64 -> RI.rsapss_pkey_verify_st U64 (BE.mk_runtime_exp_uint64 len).BE.mont.BM.bn.BN.len
let rsapss_pkey_verify len a modBits eBits nb eb sLen k sgnt msgLen msg =
  RI.rsapss_pkey_verify
    (BE.mk_runtime_exp_uint64 len)
     RK.mk_runtime_rsapss_load_keys_uint64
    (RI.mk_runtime_rsapss_uint64 len)
     a modBits eBits nb eb sLen k sgnt msgLen msg
