module Spec.Hash.Incremental.Lemmas

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.Incremental

let hash = Spec.Agile.Hash.hash

val hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
