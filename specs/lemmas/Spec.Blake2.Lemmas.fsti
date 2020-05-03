module Spec.Blake2.Lemmas

module U32 = FStar.UInt32

open Spec.Hash.Definitions
open Spec.Agile.Hash
open FStar.Mul

noextract inline_for_extraction
val add_extra_i (a:hash_alg{is_blake a}) (ev:extra_state a) (i:U32.t) : extra_state a

val add_extra_i_zero (a:hash_alg{is_blake a}) (ev:extra_state a):
  Lemma (add_extra_i a ev 0ul == ev)

val update_multi_add_extra (a:hash_alg{is_blake a})
  (h: words_state a)
  (i:nat)
  (input: bytes_blocks a):
  Lemma
  (requires i + 1 < pow2 32 /\ Seq.length input = block_length a * i)
  (ensures
    (
     let h' = update_multi a h input in
     snd h' == add_extra_i a (snd h) (U32.uint_to_t i)))
  (decreases i)
