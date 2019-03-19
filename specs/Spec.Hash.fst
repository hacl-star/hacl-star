module Spec.Hash

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish

let init a: init_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.init a
  | MD5 ->
      Spec.MD5.init
  | SHA1 ->
      Spec.SHA1.init

let update a: update_t a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.update a
  | MD5 ->
      Spec.MD5.update
  | SHA1 ->
      Spec.SHA1.update

(* A helper that deals with the modulo proof obligation to make things go smoothly. *)
let split_block (a: hash_alg)
  (blocks: bytes_blocks a)
  (n: nat{n <= S.length blocks / block_length a}):
  Tot (p:(Spec.Hash.Definitions.bytes_blocks a * Spec.Hash.Definitions.bytes_blocks a)
         {fst p == fst (Seq.split blocks (FStar.Mul.(n * block_length a))) /\
	  snd p == snd (Seq.split blocks (FStar.Mul.(n * block_length a)))})
=
  let block, rem = S.split blocks FStar.Mul.(n * block_length a) in
  assert (S.length rem = S.length blocks - S.length block);
  Math.Lemmas.modulo_distributivity (S.length rem) (S.length block) (block_length a);
  assert (S.length rem % block_length a = 0);
  block, rem

(* Compression function for multiple blocks. Note: this one could be
 * parameterized over any update function and the lemma would still be provable,
 * but that's perhaps too much hassle. *)
let rec update_multi
  (a:hash_alg)
  (hash:words_state a)
  (blocks:bytes_blocks a):
  Tot (words_state a) (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    hash
  else
    let block, rem = split_block a blocks 1 in
    let hash = update a hash block in
    update_multi a hash rem

(* As defined in the NIST standard; pad, then update, then finish. *)
let hash (a:hash_alg) (input:bytes{S.length input < max_input_length a}):
  Tot (hash:bytes{Seq.length hash = hash_length a})
=
  let padding = pad a (S.length input) in
  finish a (update_multi a (init a) S.(input @| padding))
