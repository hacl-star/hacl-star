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

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val rsapss_sign: Hacl.Impl.RSAPSS.rsapss_sign_st
let rsapss_sign modBits eBits dBits skey sLen salt msgLen msg sgnt =
  Hacl.Impl.RSAPSS.rsapss_sign modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify: Hacl.Impl.RSAPSS.rsapss_verify_st
let rsapss_verify modBits eBits pkey sLen sgnt msgLen msg =
  Hacl.Impl.RSAPSS.rsapss_verify modBits eBits pkey sLen sgnt msgLen msg
