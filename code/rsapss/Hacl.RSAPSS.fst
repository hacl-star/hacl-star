module Hacl.RSAPSS

open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module IR = Hacl.Impl.RSAPSS
module IK = Hacl.Impl.RSAPSS.Keys

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val rsapss_sign: IR.rsapss_sign_st U64
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  [@inline_let] let ke = BE.mk_runtime_exp_uint64 (BD.blocks modBits 64ul) in
  IR.rsapss_sign ke a modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify: IR.rsapss_verify_st U64
let rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg =
  [@inline_let] let ke = BE.mk_runtime_exp_uint64 (BD.blocks modBits 64ul) in
  IR.rsapss_verify ke a modBits eBits pkey sLen k sgnt msgLen msg


val new_rsapss_load_pkey: IK.new_rsapss_load_pkey_st U64
let new_rsapss_load_pkey r modBits eBits nb eb =
  IK.new_rsapss_load_pkey r modBits eBits nb eb


val new_rsapss_load_skey: IK.new_rsapss_load_skey_st U64
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  IK.new_rsapss_load_skey r modBits eBits dBits nb eb db


val rsapss_skey_sign: IR.rsapss_skey_sign_st U64
let rsapss_skey_sign a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  [@inline_let] let ke = BE.mk_runtime_exp_uint64 (BD.blocks modBits 64ul) in
  IR.rsapss_skey_sign #U64 ke a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt


val rsapss_pkey_verify: IR.rsapss_pkey_verify_st U64
let rsapss_pkey_verify a modBits eBits nb eb sLen k sgnt msgLen msg =
  [@inline_let] let ke = BE.mk_runtime_exp_uint64 (BD.blocks modBits 64ul) in
  IR.rsapss_pkey_verify #U64 ke a modBits eBits nb eb sLen k sgnt msgLen msg
