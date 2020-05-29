module Spec.Hash.Incremental.Lemmas

module S = FStar.Seq

open Lib.IntTypes

open Spec.Hash.Definitions
open Spec.Agile.Hash
open Spec.Hash.PadFinish
open Spec.Hash.Incremental

val update_multi_extra_state_eq
  (a: hash_alg{is_blake a}) (h: words_state a)
  (input: bytes_blocks a{Seq.length input <= maxint (extra_state_int_type a)}) :
  Lemma
  (requires True)
  (ensures
    (snd (update_multi a h input) == extra_state_add_nat (snd h) (Seq.length input)))
  (decreases (Seq.length input))

val hash_incremental_block_is_update_last (a:hash_alg)
  (s:words_state a)
  (input : bytes_block a) :
  Lemma (
      (**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
      Spec.Hash.Incremental.update_last a s 0 input ==
      Spec.Hash.Incremental.hash_incremental_body a input s)

val block_hash_incremental (a:hash_alg) (input:bytes_block a)
  : Lemma
    ((**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
     finish a (update_last a (init a) 0 input) `S.equal` hash_incremental a input)

val concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ Seq.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
