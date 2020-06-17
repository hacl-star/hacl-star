module Spec.Blake2.Lemmas

module U32 = FStar.UInt32

open Spec.Hash.Definitions
open Spec.Agile.Hash
open FStar.Mul

val lemma_blake2_hash_equivalence
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) d 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)) ==
     Spec.Agile.Hash.hash a d)

/// TODO: the following is redundant with ``extra_state_add_nat``
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
