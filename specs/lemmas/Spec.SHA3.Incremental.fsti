module Spec.SHA3.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions

val sha3_is_incremental
  (a: keccak_alg)
  (input: bytes)
  (l: output_length a): Lemma (hash_incremental a input l `S.equal` hash' a input l)
