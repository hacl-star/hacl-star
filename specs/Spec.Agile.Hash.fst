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
  | Blake2S -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2S 0 32, u64 0
  | Blake2B -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2B 0 64, u128 0
  | SHA3_256 -> Lib.Sequence.create 25 (u64 0), ()

val update_sha3_256: update_t SHA3_256
let update_sha3_256 (s: words_state SHA3_256) (b: bytes { Seq.length b = block_length SHA3_256 }) =
  let s, () = s in
  let rateInBytes = 1088 / 8 in
  Spec.SHA3.absorb_inner rateInBytes b s, ()

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
      // We should never have overflows given the restriction on buffer lengths, so
      // this should be equivalent to a nat addition
      let totlen = extra_state_add_nat totlen (size_block a) in
      (Spec.Blake2.blake2_update_block Spec.Blake2.Blake2S false (extra_state_v totlen) l blake_state,
       totlen)
  | Blake2B -> fun h l ->
      let blake_state, totlen = h in
      // We should never have overflows given the restriction on buffer lengths, so
      // this should be equivalent to a nat addition
      let totlen = extra_state_add_nat totlen (size_block a) in
      (Spec.Blake2.blake2_update_block Spec.Blake2.Blake2B false (extra_state_v totlen) l blake_state,
       totlen)
  | SHA3_256 -> update_sha3_256

let update_multi
  (a:hash_alg)
  (hash:words_state a)
  (blocks:bytes_blocks a)
=
  Lib.UpdateMulti.mk_update_multi (block_length a) (update a) hash blocks

#push-options "--fuel 0 --ifuel 0"

// MD hashes are by definition the application of init / update_multi / pad / finish.
// Blake2 does its own thing, and there is a slightly more involved proof that the hash is incremental.
// Same deal with the SHA3 family.
let hash (a:hash_alg) (input:bytes{S.length input `less_than_max_input_length` a})
  =
  if is_blake a then
    Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a))
  else if is_sha3 a then
    // TODO: refine for other SHAs here
    Spec.SHA3.sha3_256 (Seq.length input) input
  else
    (* As defined in the NIST standard; pad, then update, then finish. *)
    let padding = pad a (S.length input) in
    finish a (update_multi a (init a) S.(input @| padding))
