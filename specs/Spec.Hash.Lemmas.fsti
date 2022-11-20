module Spec.Hash.Lemmas

module S = FStar.Seq

open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
include Spec.Hash.Lemmas0

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// First hash law.
val update_multi_zero (a: hash_alg) (h: words_state a): Lemma
  (requires update_multi_pre a h S.empty)
  (ensures ((update_multi a h S.empty) == h))
  [ SMTPat (update_multi a h S.empty) ]

/// Second hash law. MD hashes defer to Lib.UpdateMulti while Blake2 and SHA3 defer to Lib.SequenceLemmas.
val update_multi_associative (a: hash_alg)
  (h: words_state a)
  (input1: bytes)
  (input2: bytes):
  Lemma
  (requires (
    S.length input1 % block_length a == 0 /\
    S.length input2 % block_length a == 0 /\
    update_multi_pre a h (S.append input1 input2)))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a == 0 /\
    update_multi_pre a h input1 /\
    update_multi_pre a (update_multi a h input1) input2 /\
    update_multi a (update_multi a h input1) input2 == update_multi a h input))
  [ SMTPat (update_multi a (update_multi a h input1) input2) ]

val block_length_smaller_than_max_input (a:hash_alg) :
  Lemma (block_length a `less_than_max_input_length` a)
