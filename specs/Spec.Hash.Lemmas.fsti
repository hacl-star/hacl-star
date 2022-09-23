module Spec.Hash.Lemmas

module S = FStar.Seq

open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
include Spec.Hash.Lemmas0

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

val extra_state_add_nat_bound_lem1 (#a:hash_alg{is_blake a}) (s : extra_state a)
                                   (n:nat{n <= max_extra_state a}) :
  Lemma
  (requires extra_state_v s + n <= max_extra_state a)
  (ensures extra_state_v (extra_state_add_nat s n) = extra_state_v s + n)

val extra_state_add_nat_bound_lem2 (#a:hash_alg{is_blake a}) (s : extra_state a)
                                   (n:nat{n <= max_extra_state a}) :
  Lemma
  (requires extra_state_v s + n <= max_extra_state a)
  (ensures extra_state_add_nat s n == nat_to_extra_state a ((extra_state_v s) + n))

val extra_state_add_nat_bound_associative_lem (#a:hash_alg{is_blake a}) (s : extra_state a)
                                              (n1 n2 : range_t (extra_state_int_type a)) :
  Lemma
  (requires n1 + n2 <= max_extra_state a)
  (ensures
       (extra_state_add_nat (extra_state_add_nat s n1) n2 ==
        extra_state_add_nat s (n1 + n2)))

val extra_state_v_of_nat (a:hash_alg{is_blake a})
                         (n:nat{n <= max_extra_state a}) :
  Lemma(extra_state_v (nat_to_extra_state a n) = n)

/// The following lemmas allow to reason about [update_multi]
val update_multi_zero (a: hash_alg) (h: words_state a): Lemma
  (ensures ((update_multi a h S.empty) == h))
  [ SMTPat (update_multi a h S.empty) ]

val update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures ((update_multi a h input) == (update a h input)))
  [ SMTPat (update a h input) ]

/// Legacy formulation of this lemma. See Lib.UpdateMulti for a more generic
/// version that avoids a delicate proof obligation in the post-condition -- use
/// the version from Lib.UpdateMulti whenever possible.
val update_multi_associative (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a = 0 /\
    (update_multi a (update_multi a h input1) input2) ==
      (update_multi a h input)))
  [ SMTPat (update_multi a (update_multi a h input1) input2) ]

val block_length_smaller_than_max_input (a:hash_alg) :
  Lemma(block_length a <= max_input_length a)

val pad_invariant_block (a: md_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % block_length a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))

val reveal_init_blake2 (a : Spec.Blake2.alg): Lemma (
  let ws: words_state' (to_hash_alg a) = Spec.Blake2.blake2_init_hash a 0 (Spec.Blake2.max_output a) in
  Spec.Agile.Hash.init (to_hash_alg a) == (ws, nat_to_extra_state (to_hash_alg a) 0))
