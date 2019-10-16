module Spec.Hash.Lemmas

module S = FStar.Seq

include Spec.Hash.Lemmas0

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental
open Spec.Hash.PadFinish

val update_multi_zero (a: hash_alg) (h: words_state a): Lemma
  (ensures (S.equal (update_multi a h S.empty) h))
  [ SMTPat (update_multi a h S.empty) ]

val update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (S.equal (update_multi a h input) (update a h input)))
  [ SMTPat (update a h input) ]

val update_multi_block (a: hash_alg) (h: words_state a) (input: bytes):
  Lemma
    (requires (
      S.length input % block_length a = 0 /\
      block_length a <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input 1 in
      (update_multi a (update_multi a h input1) input2) == (update_multi a h input)))

val update_multi_associative:
  a: hash_alg ->
  h: words_state a ->
  input: bytes ->
  len: nat ->
  Lemma
    (requires (
      len % block_length a = 0 /\
      S.length input % block_length a = 0 /\
      len <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input (len / block_length a) in
      S.equal (update_multi a (update_multi a h input1) input2)
        (update_multi a h input)))
    (decreases (
      %[ S.length input; len ]))

val update_multi_associative' (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    S.equal (update_multi a (update_multi a h input1) input2)
      (update_multi a h input)))
  [ SMTPat (update_multi a (update_multi a h input1) input2) ]

let hash = Spec.Agile.Hash.hash

val hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
