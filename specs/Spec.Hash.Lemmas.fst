module Spec.Hash.Lemmas

module S = FStar.Seq
open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

friend Spec.Agile.Hash

(** Lemmas about the behavior of update_multi / update_last *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"

let update_multi_zero (a: hash_alg) h =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
    Lib.UpdateMulti.update_multi_zero (block_length a) (Spec.Agile.Hash.update a) h
  | Blake2B | Blake2S ->
    Lib.LoopCombinators.eq_repeati0 (0 / block_length a) (Spec.Blake2.blake2_update1 (to_blake_alg a) (init_extra_state a) S.empty) h
  | SHA3_256 ->
    let rateInBytes = 1088/8 in
    let f = Spec.SHA3.absorb_inner rateInBytes in
    Lib.Sequence.lemma_repeat_blocks_multi rateInBytes S.empty f h;

    let nb = 0 / rateInBytes in
    Lib.LoopCombinators.eq_repeati0 nb (Lib.Sequence.repeat_blocks_f rateInBytes S.empty f nb) h

(*
let update_multi_associative_blake2 (a: blake_alg)
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
  =
  admit()
*)

let update_multi_associative (a: hash_alg)
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
  = admit()

(*
let update_multi_associative (a: hash_alg)
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
=
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
    Lib.UpdateMulti.update_multi_associative (block_length a) (Spec.Agile.Hash.update a) h input1 input2
  | Blake2B | Blake2S ->
    update_multi_associative_blake2 a h input1 input2
  | SHA3_256 ->
    let rateInBytes = 1088/8 in
    let f = Spec.SHA3.absorb_inner rateInBytes in
    let input = input1 `S.append` input2 in
    assert (input1 `S.equal` S.slice input 0 (S.length input1));
    assert (input2 `S.equal` S.slice input (S.length input1) (S.length input));
    Lib.Sequence.Lemmas.repeat_blocks_multi_split (block_length a) (S.length input1) input f h
*)

(* *)
let block_length_smaller_than_max_input (a:hash_alg) =
  normalize_term_spec(pow2 61 - 1);
  normalize_term_spec(pow2 125 - 1);
  normalize_term_spec(pow2 64 - 1)
