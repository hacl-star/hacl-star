module Spec.Hash

module S = FStar.Seq

open Spec.Hash.Helpers

(** These will eventually multiplex between SHA2, SHA1, MD5 *)

let init a: init_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.init a

let update a: update_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.update a

let pad a: pad_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.pad a

let finish a: finish_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.finish a

(* A helper that deals with the modulo proof obligation to make things go smoothly. *)
let split_block (a: hash_alg)
  (blocks: bytes_blocks a)
  (n: nat{n <= S.length blocks / size_block a}):
  Tot (bytes_blocks a * bytes_blocks a)
=
  let block, rem = S.split blocks FStar.Mul.(n * size_block a) in
  assert (S.length rem = S.length blocks - S.length block);
  Math.Lemmas.modulo_distributivity (S.length rem) (S.length block) (size_block a);
  assert (S.length rem % size_block a = 0);
  block, rem

(* Compression function for multiple blocks. Note: this one could be
 * parameterized over any update function and the lemma would still be provable,
 * but that's perhaps too much hassle. *)
let rec update_multi
  (a:hash_alg)
  (hash:hash_w a)
  (blocks:bytes_blocks a):
  Tot (hash_w a) (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    hash
  else
    let block, rem = split_block a blocks 1 in
    let hash = update a hash block in
    update_multi a hash rem

(** Lemmas about the behavior of update_multi / update_last *)

let update_multi_zero (a: hash_alg) (h: hash_w a): Lemma
  (ensures (S.equal (update_multi a h S.empty) h))
  [ SMTPat (update_multi a h S.empty) ]
=
  ()

#set-options "--z3rlimit 50"

let update_multi_block (a: hash_alg) (h: hash_w a) (input: bytes):
  Lemma
    (requires (
      S.length input % size_block a = 0 /\
      size_block a <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input 1 in
      (update_multi a (update_multi a h input1) input2) == (update_multi a h input)))
=
  ()

#set-options "--max_fuel 0 --max_ifuel 0"

val update_multi_associative:
  a: hash_alg ->
  h: hash_w a ->
  input: bytes ->
  len: nat ->
  Lemma
    (requires (
      len % size_block a = 0 /\
      S.length input % size_block a = 0 /\
      len <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input (len / size_block a) in
      S.equal (update_multi a (update_multi a h input1) input2)
        (update_multi a h input)))
    (decreases (
      %[ S.length input; len ]))

let rec update_multi_associative a h input len =
  let i_l, i_r = S.split input len in
  let n = len / size_block a in
  if len = 0 then begin
    assert (S.equal i_l S.empty);
    assert (S.equal i_r input);
    update_multi_zero a h
  end else if len = size_block a then begin
    update_multi_block a h input
  end else begin
    let i0, _ = split_block a i_l (n - 1) in
    let _, i3 = split_block a input (n - 1) in
    update_multi_associative a h i_l (len - size_block a);
    update_multi_associative a (update_multi a h i0) i3 (size_block a);
    update_multi_associative a h input (len - size_block a)
  end

(* In a form more suitable to SMTPat *)
let update_multi_associative' (a: hash_alg)
  (h: hash_w a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    S.equal (update_multi a (update_multi a h input1) input2)
      (update_multi a h input)))
  [ SMTPat (update_multi a (update_multi a h input1) input2) ]
=
  let input = S.append input1 input2 in
  let input1', input2' = split_block a input (S.length input1 / size_block a) in
  assert (Seq.equal input1 input1');
  assert (Seq.equal input2 input2');
  update_multi_associative a h input (S.length input1)
