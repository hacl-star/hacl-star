module Spec.Frodo.KEM

open Lib.IntTypes
open Lib.Sequence

open FStar.Mul

open Spec.Matrix
open Spec.Frodo.Params

let bytes_mu: size_nat =
  params_extracted_bits * params_nbar * params_nbar / 8

let crypto_publickeybytes: size_nat =
  bytes_seed_a + params_logq * params_n * params_nbar / 8

let crypto_secretkeybytes: size_nat =
  crypto_bytes + crypto_publickeybytes + 2 * params_n * params_nbar

let crypto_ciphertextbytes: size_nat =
  (params_nbar * params_n + params_nbar * params_nbar) * params_logq / 8 + crypto_bytes

val expand_crypto_publickeybytes: unit -> Lemma
   (crypto_publickeybytes ==
     bytes_seed_a + params_logq * params_n * params_nbar / 8)
let expand_crypto_publickeybytes _ = ()

val expand_crypto_secretkeybytes: unit -> Lemma
   (crypto_secretkeybytes ==
     crypto_bytes + crypto_publickeybytes + 2 * params_n * params_nbar)
let expand_crypto_secretkeybytes _ = ()

val expand_crypto_ciphertextbytes: unit -> Lemma
   (crypto_ciphertextbytes ==
    params_logq * params_nbar * params_n / 8
    + (params_logq * params_nbar * params_nbar / 8 + crypto_bytes))
let expand_crypto_ciphertextbytes _ =
  assert ((params_nbar * params_n + params_nbar * params_nbar) * params_logq =
    params_logq * params_nbar * params_n + params_logq * params_nbar * params_nbar)
