module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Incremental.Definitions
open FStar.Mul

val blake2_is_hash_incremental
  (a : blake_alg)
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma (
    S.equal (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)))
            (hash_incremental a input ()))
