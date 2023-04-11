module Spec.Hash.Incremental

module S = FStar.Seq
module Blake2 = Spec.Blake2

open Spec.Agile.Hash
open Spec.Hash.Definitions

open FStar.Mul
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

module Loops = Lib.LoopCombinators
module UpdateMulti = Lib.UpdateMulti

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// A declaration whose sole purpose is to force synchronize the .fst and the .fsti
[@must_erase_for_extraction]
private val _sync_decl : Type0

include Spec.Hash.Incremental.Definitions

val hash_is_hash_incremental' (a: hash_alg) (input: bytes { S.length input `less_than_max_input_length` a })
  (l: output_length a):
  Lemma (S.equal (hash' a input l) (hash_incremental a input l))

unfold
let hash_is_hash_incremental (a: fixed_len_alg) (input: bytes { S.length input `less_than_max_input_length` a }) =
  hash_is_hash_incremental' a input ()
