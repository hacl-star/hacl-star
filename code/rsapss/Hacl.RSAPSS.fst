module Hacl.RSAPSS

open FStar.Mul
open Lib.IntTypes

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module RI = Hacl.Impl.RSAPSS
module RK = Hacl.Impl.RSAPSS.Keys

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.ExponentiationPrecomp
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let modBits_t = RI.modBits_t t_limbs

inline_for_extraction noextract
let ke (modBits:modBits_t) =
  BE.mk_runtime_exp #t_limbs (BD.blocks modBits (size (bits t_limbs)))


private
[@CInline]
let load_pkey (modBits:modBits_t) : RK.rsapss_load_pkey_st t_limbs (ke modBits) modBits =
  RK.rsapss_load_pkey (ke modBits) modBits RK.mk_runtime_rsapss_checks

private
[@CInline]
let load_skey (modBits:modBits_t) : RK.rsapss_load_skey_st t_limbs (ke modBits) modBits =
  RK.rsapss_load_skey (ke modBits) modBits RK.mk_runtime_rsapss_checks (load_pkey modBits)


val rsapss_sign:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_sign_st t_limbs (ke modBits) a modBits

let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  RI.rsapss_sign (ke modBits) a modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_verify_st t_limbs (ke modBits) a modBits

let rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg =
  RI.rsapss_verify (ke modBits) a modBits eBits pkey sLen k sgnt msgLen msg


val new_rsapss_load_pkey: modBits:modBits_t -> RK.new_rsapss_load_pkey_st t_limbs (ke modBits) modBits
let new_rsapss_load_pkey modBits r eBits nb eb =
  RK.new_rsapss_load_pkey (ke modBits) modBits (load_pkey modBits) r eBits nb eb


val new_rsapss_load_skey: modBits:modBits_t -> RK.new_rsapss_load_skey_st t_limbs (ke modBits) modBits
let new_rsapss_load_skey modBits r eBits dBits nb eb db =
  RK.new_rsapss_load_skey (ke modBits) modBits (load_skey modBits) r eBits dBits nb eb db


val rsapss_skey_sign:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_skey_sign_st t_limbs (ke modBits) a modBits

let rsapss_skey_sign a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  RI.rsapss_skey_sign (ke modBits) a modBits
    (load_skey modBits) (rsapss_sign a modBits) eBits dBits nb eb db sLen salt msgLen msg sgnt


val rsapss_pkey_verify:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_pkey_verify_st t_limbs (ke modBits) a modBits

let rsapss_pkey_verify a modBits eBits nb eb sLen k sgnt msgLen msg =
  RI.rsapss_pkey_verify (ke modBits) a modBits
    (load_pkey modBits) (rsapss_verify a modBits) eBits nb eb sLen k sgnt msgLen msg
