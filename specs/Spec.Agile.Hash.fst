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
  | Blake2B -> Spec.Blake2.blake2_init Spec.Blake2.Blake2B 0 Seq.empty 64, u64 0

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
      (Spec.Blake2.blake2_update_block Spec.Blake2.Blake2B false (v #U64 #SEC totlen) l blake_state,
      // We should never have overflows given the restriction on buffer lengths, so
      // this should be equivalent to a nat addition
       totlen +. u64 (size_block a))


let update_multi
  (a:hash_alg)
  (hash:words_state a)
  (blocks:bytes_blocks a)
=
  Lib.UpdateMulti.mk_update_multi (block_length a) (update a) hash blocks

#push-options "--fuel 0 --ifuel 0"

let hash (a:hash_alg) (input:bytes{S.length input <= max_input_length a})
  =
  if is_blake a then
    Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a))
  else
    (* As defined in the NIST standard; pad, then update, then finish. *)
    let padding = pad a (S.length input) in
    finish a (update_multi a (init a) S.(input @| padding))
