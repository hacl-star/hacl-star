module Hacl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Impl.MGF

module ST = FStar.HyperStack.ST
module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val rsapss_sign: a:Hash.algorithm{S.hash_is_supported a} -> Hacl.Impl.RSAPSS.rsapss_sign_st a
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  Hacl.Impl.RSAPSS.rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify: a:Hash.algorithm{S.hash_is_supported a} -> Hacl.Impl.RSAPSS.rsapss_verify_st a
let rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg =
  Hacl.Impl.RSAPSS.rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg
