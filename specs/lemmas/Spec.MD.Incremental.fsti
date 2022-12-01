module Spec.MD.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

val md_is_hash_incremental
  (a:hash_alg{is_md a})
  (input: bytes { S.length input `less_than_max_input_length` a })
  (s:words_state a)
  : Lemma (
      let blocks, rest = split_blocks a input in
      update_multi a s (input `S.append` (pad a (S.length input))) ==
      update_last a (update_multi a s blocks) (S.length blocks) rest)
