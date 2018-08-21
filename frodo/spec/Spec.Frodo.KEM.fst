module Spec.Frodo.KEM

open Lib.IntTypes
open Lib.Sequence

open FStar.Mul

open Spec.Matrix
open Spec.Frodo.Params
open Spec.Frodo.Clear

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

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
let expand_crypto_ciphertextbytes _ = ()

val clear_matrix:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 < max_size_t /\ n1 * n2 % 2 = 0}
  -> m:matrix n1 n2
  -> matrix n1 n2
let clear_matrix #n1 #n2 m =
  clear_words_u16 (n1 * n2) m
