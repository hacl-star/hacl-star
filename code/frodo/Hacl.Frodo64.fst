module Hacl.Frodo64

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Frodo.KEM
open Hacl.Impl.Frodo.Params

module FP = Spec.Frodo.Params

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@@ CPrologue
"/*
 this variant is used only for testing purposes!
 */\n" ]


let crypto_bytes :r:size_t{v r == FP.crypto_bytes FP.Frodo64} =
  crypto_bytes FP.Frodo64

let crypto_publickeybytes :r:size_t{v r == FP.crypto_publickeybytes FP.Frodo64} =
  normalize_term (crypto_publickeybytes FP.Frodo64)

let crypto_secretkeybytes :r:size_t{v r == FP.crypto_secretkeybytes FP.Frodo64} =
  normalize_term (crypto_secretkeybytes FP.Frodo64)

let crypto_ciphertextbytes :r:size_t{v r == FP.crypto_ciphertextbytes FP.Frodo64} =
  normalize_term (crypto_ciphertextbytes FP.Frodo64)


val crypto_kem_keypair: crypto_kem_keypair_st FP.Frodo64 FP.SHAKE128
let crypto_kem_keypair pk sk =
  crypto_kem_keypair FP.Frodo64 FP.SHAKE128 pk sk

val crypto_kem_enc: crypto_kem_enc_st FP.Frodo64 FP.SHAKE128
let crypto_kem_enc ct ss pk =
  crypto_kem_enc FP.Frodo64 FP.SHAKE128 ct ss pk

val crypto_kem_dec: crypto_kem_dec_st FP.Frodo64 FP.SHAKE128
let crypto_kem_dec ss ct sk =
  crypto_kem_dec FP.Frodo64 FP.SHAKE128 ss ct sk
