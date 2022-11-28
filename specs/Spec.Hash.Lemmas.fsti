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
  (requires update_multi_pre a h (init_extra_state a) S.empty)
  (ensures ((update_multi a h (init_extra_state a) S.empty) == h))
  [ SMTPat (update_multi a h (init_extra_state a) S.empty) ]

/// Second hash law. MD hashes defer to Lib.UpdateMulti while Blake2 and SHA3 defer to Lib.SequenceLemmas.
val update_multi_associative (a: hash_alg{not (is_blake a)})
  (h: words_state a)
  (input1: bytes)
  (input2: bytes):
  Lemma
  (requires
    S.length input1 % block_length a == 0 /\
    S.length input2 % block_length a == 0)
  (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a == 0 /\
    update_multi a (update_multi a h () input1) () input2 == update_multi a h () input))
  [ SMTPat (update_multi a (update_multi a h () input1) () input2) ]

val update_multi_associative_blake (a: blake_alg)
  (h: words_state a)
  (prevlen1: nat)
  (prevlen2: nat)
  (input1: bytes)
  (input2: bytes):
  Lemma
  (requires (
    prevlen1 % block_length a = 0 /\
    S.length input1 % block_length a == 0 /\
    S.length input2 % block_length a == 0 /\
    prevlen2 = prevlen1 + S.length input1 /\
    update_multi_pre a h prevlen1 (S.append input1 input2)))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a == 0 /\
    update_multi_pre a h prevlen1 input1 /\
    update_multi_pre a (update_multi a h prevlen1 input1) prevlen2 input2 /\
    update_multi a (update_multi a h prevlen1 input1) prevlen2 input2 == update_multi a h prevlen1 input))
  [ SMTPat (update_multi a (update_multi a h prevlen1 input1) prevlen2 input2) ]

val block_length_smaller_than_max_input (a:hash_alg) :
  Lemma (block_length a `less_than_max_input_length` a)
