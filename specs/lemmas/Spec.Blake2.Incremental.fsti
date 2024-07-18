module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Incremental.Definitions
open FStar.Mul

val blake2_is_hash_incremental
  (a : blake_alg)
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma (
    S.equal (Spec.Blake2.blake2 (to_blake_alg a) false input
              (Spec.Blake2.blake2_default_params (to_blake_alg a))
              Seq.empty)
            (hash_incremental a input ()))
