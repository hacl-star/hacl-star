module Spec.Hash.Lemmas

module S = FStar.Seq

include Spec.Hash.Lemmas0

open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

friend Spec.Agile.Hash

let extra_state_add_nat_bound_lem (#a:hash_alg{is_blake a}) (s : extra_state a)
                                  (n:nat{n <= maxint (extra_state_int_type a)}) :
  Lemma
  (requires extra_state_v s + n <= maxint (extra_state_int_type a))
  (ensures extra_state_v (extra_state_add_nat s n) ==
             extra_state_v s + n) = ()

let extra_state_add_nat_bound_associative_lem (#a:hash_alg{is_blake a}) (s : extra_state a)
                                              (n1 n2 : range_t (extra_state_int_type a)) :
  Lemma
  (requires n1 + n2 <= maxint (extra_state_int_type a))
  (ensures
       (extra_state_add_nat (extra_state_add_nat s n1) n2 ==
        extra_state_add_nat s (n1 + n2))) =
  let s1 = extra_state_add_nat s n1 in
  let s2 = extra_state_add_nat s1 n2 in
  let s3 = extra_state_add_nat s (n1 + n2) in
  let s1_v = extra_state_v s1 in
  let s2_v = extra_state_v s2 in
  let s3_v = extra_state_v s3 in
  assert(extra_state_add_nat (extra_state_add_nat s n1) n2 ==
          (s +. nat_to_extra_state a n1) +. nat_to_extra_state a n2);
  assert(s1_v == (extra_state_v s + n1) @%. U64);
  assert(s2_v == s1_v + n2 @%. U64);
  assert(s2_v == (s1_v + n2) % modulus U64);
  Math.Lemmas.lemma_mod_add_distr n2 (extra_state_v s + n1) (modulus U64);
  assert(s2_v == (extra_state_v s + n1 + n2) % modulus U64);
  Math.Lemmas.lemma_mod_add_distr (extra_state_v s) (n1 + n1) (modulus U64);
  assert(s3_v == (extra_state_v s + n1 + n2) % modulus U64);
  assert(s2_v == s3_v)


(* Lemmas such as: relationship between maximum lengths, incremental API vs.
 * NIST reference, etc. *)

(** Lemmas about the behavior of update_multi / update_last *)

let update_multi_zero (a: hash_alg) = Lib.UpdateMulti.update_multi_zero (block_length a) (Spec.Agile.Hash.update a)

let update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (update_multi a h input) == (update a h input))
=
  ()

let update_multi_associative (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    (update_multi a (update_multi a h input1) input2) ==
      (update_multi a h input)))
=
  Lib.UpdateMulti.update_multi_associative (block_length a) (Spec.Agile.Hash.update a) h input1 input2
