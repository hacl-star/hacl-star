module Spec.SHA3.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

val sha3_is_incremental
  (a: sha3_alg)
  (input: bytes): Lemma (hash_incremental a input `S.equal` hash a input)
