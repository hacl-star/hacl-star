module Spec.Hash.Incremental.Lemmas

module S = FStar.Seq

open Lib.IntTypes

open Spec.Hash.Definitions
open Spec.Agile.Hash
open Spec.Hash.PadFinish
open Spec.Hash.Incremental

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val update_multi_extra_state_eq
  (a: hash_alg{is_blake a}) (h: words_state a)
  (input: bytes_blocks a{Seq.length input <= max_extra_state a}) :
  Lemma
  (requires True)
  (ensures
    (snd (update_multi a h input) == extra_state_add_nat (snd h) (Seq.length input)))

val hash_incremental_block_is_update_last (a:hash_alg)
  (s:words_state a)
  (input : bytes_block a) :
  Lemma (
      (**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
      Spec.Hash.Incremental.update_last a s 0 input ==
      Spec.Hash.Incremental.hash_incremental_body a input s)

val block_hash_incremental (a:hash_alg) (input:bytes_block a)
  : Lemma
    ((**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
     finish a (update_last a (init a) 0 input) `S.equal` hash_incremental a input)

val lemma_split_blocks_assoc (a:hash_alg) (s1 s2:bytes)
  : Lemma
      (requires
        (S.length s1 + S.length s2) `less_than_max_input_length` a /\
        S.length s1 % block_length a == 0 /\ S.length s2 > 0)
      (ensures (
        let b1, l1 = split_blocks a (s1 `S.append` s2) in
        let b2, l2 = split_blocks a s2 in
        b1 == s1 `S.append` b2 /\ l1 == l2))
