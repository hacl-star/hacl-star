module Spec.Hash.Lemmas

module S = FStar.Seq

include Spec.Hash.Lemmas0

open Spec.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental
open Spec.Hash.PadFinish

(* Lemmas such as: relationship between maximum lengths, incremental API vs.
 * NIST reference, etc. *)

(** Lemmas about the behavior of update_multi / update_last *)

let update_multi_zero (a: hash_alg) (h: words_state a): Lemma
  (ensures (S.equal (update_multi a h S.empty) h))
  [ SMTPat (update_multi a h S.empty) ]
=
  ()

#set-options "--z3rlimit 50"

let update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (S.equal (update_multi a h input) (update a h input)))
  [ SMTPat (update a h input) ]
=
  ()

/// Start of the central proof of the commutation of update_multi and append

(** A small helper. *)
let update_multi_block (a: hash_alg) (h: words_state a) (input: bytes):
  Lemma
    (requires (
      S.length input % block_length a = 0 /\
      block_length a <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input 1 in
      (update_multi a (update_multi a h input1) input2) == (update_multi a h input)))
=
  ()

#set-options "--max_fuel 0 --max_ifuel 0"

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

let rec update_multi_associative a h input len =
  let i_l, i_r = S.split input len in
  let n = len / block_length a in
  if len = 0 then begin
    assert (S.equal i_l S.empty);
    assert (S.equal i_r input);
    update_multi_zero a h
  end else if len = block_length a then begin
    update_multi_block a h input
  end else begin
    let i0, _ = split_block a i_l (n - 1) in
    let _, i3 = split_block a input (n - 1) in
    update_multi_associative a h i_l (len - block_length a);
    update_multi_associative a (update_multi a h i0) i3 (block_length a);
    update_multi_associative a h input (len - block_length a)
  end

(* In a form more suitable to SMTPat *)
let update_multi_associative' (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    S.equal (update_multi a (update_multi a h input1) input2)
      (update_multi a h input)))
  [ SMTPat (update_multi a (update_multi a h input1) input2) ]
=
  let input = S.append input1 input2 in
  let input1', input2' = split_block a input (S.length input1 / block_length a) in
  assert (Seq.equal input1 input1');
  assert (Seq.equal input2 input2');
  update_multi_associative a h input (S.length input1)

#set-options "--max_fuel 0 --max_ifuel 0"

let hash = Spec.Hash.hash

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input < max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
=
  let open FStar.Mul in
  let n = S.length input / block_length a in
  // From hash:
  let padded_input = S.(input @| pad a (S.length input)) in
  let blocks, rest = split_block a padded_input n in
  update_multi_associative a (init a) padded_input (n * block_length a);
  assert (hash a input == finish a (update_multi a (update_multi a (init a) blocks) rest));
  // From hash_incremental:
  let blocks', rest' = S.split input (n * block_length a) in
  assert (hash_incremental a input ==
    finish a (update_last a (update_multi a (init a) blocks') (n * block_length a) rest'));
  // Then.
  assert (Seq.equal blocks blocks');
  assert (Seq.equal rest S.(rest' @| pad a (length input)));
  assert (
    let padding = pad a (S.length input) in
    hash_incremental a input ==
    finish a (update_multi a (update_multi a (init a) blocks) rest));
  ()
