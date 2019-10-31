module Spec.Frodo.Params

open Lib.IntTypes
open FStar.Mul

open Frodo.Params

unfold let v = size_v

let params_n = v params_n

let params_logq = v params_logq

let params_extracted_bits = v params_extracted_bits

let crypto_bytes = v crypto_bytes

let bytes_seed_a = v bytes_seed_a

let params_nbar = v params_nbar

unfold let frodo_prf_spec = frodo_prf_spec

unfold let frodo_gen_matrix = frodo_gen_matrix

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
