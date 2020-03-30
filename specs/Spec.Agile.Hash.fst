module Spec.Agile.Hash

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul
open Lib.IntTypes

let init a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.init a
  | MD5 ->
      Spec.MD5.init
  | SHA1 ->
      Spec.SHA1.init
  | Blake2S -> Spec.Blake2.blake2_init Spec.Blake2.Blake2S 0 Seq.empty 32, u64 0
  | Blake2B -> Spec.Blake2.blake2_init Spec.Blake2.Blake2B 0 Seq.empty 64, u128 0

let update a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.update a
  | MD5 ->
      Spec.MD5.update
  | SHA1 ->
      Spec.SHA1.update
  | Blake2S -> fun h l ->
      let blake_state, totlen = h in
      (Spec.Blake2.blake2_update_block Spec.Blake2.Blake2S false (v #U64 #SEC totlen) l blake_state,
      // We should never have overflows given the restriction on buffer lengths, so
      // this should be equivalent to a nat addition
       totlen +. u64 (size_block a))
  | Blake2B -> fun h l ->
      let blake_state, totlen = h in
      (Spec.Blake2.blake2_update_block Spec.Blake2.Blake2B false (v #U128 #SEC totlen) l blake_state,
      // We should never have overflows given the restriction on buffer lengths, so
      // this should be equivalent to a nat addition
       totlen +. u128 (size_block a))


(* A helper that deals with the modulo proof obligation to make things go smoothly. *)
let split_block (a: hash_alg)
  (blocks: bytes_blocks a)
  (n: nat{n <= S.length blocks / block_length a}):
  Tot (p:(Spec.Hash.Definitions.bytes_blocks a & Spec.Hash.Definitions.bytes_blocks a)
         {fst p == fst (Seq.split blocks (n * block_length a)) /\
	  snd p == snd (Seq.split blocks (n * block_length a))})
= let block, rem = S.split blocks (n * block_length a) in
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
  (blocks:bytes_blocks a)
  =
  if S.length blocks = 0 then
    hash
  else
    let block, rem = split_block a blocks 1 in
    let hash = update a hash block in
    update_multi a hash rem

(* As defined in the NIST standard; pad, then update, then finish. *)
let hash (a:hash_alg) (input:bytes{S.length input <= max_input_length a})
  =
  let padding = pad a (S.length input) in
  finish a (update_multi a (init a) S.(input @| padding))
