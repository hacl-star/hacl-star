module Spec.Hash.Lemmas

module S = FStar.Seq

include Spec.Hash.Lemmas0

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

friend Spec.Agile.Hash

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
