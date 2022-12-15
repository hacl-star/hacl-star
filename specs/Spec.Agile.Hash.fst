module Spec.Agile.Hash

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul
open Lib.IntTypes

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

let init a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.init a
  | MD5 ->
      Spec.MD5.init
  | SHA1 ->
      Spec.SHA1.init
  | Blake2S -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2S 0 32
  | Blake2B -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2B 0 64
  | SHA3_256 -> Lib.Sequence.create 25 (u64 0)

// Intentionally restricting this one to MD hashes... we want clients to AVOID
// juggling between mk_update_multi update vs. repeati for non-MD hashes.
let update (a: md_alg) =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.update a
  | MD5 ->
      Spec.MD5.update
  | SHA1 ->
      Spec.SHA1.update

let update_multi a hash prev blocks =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Lib.UpdateMulti.mk_update_multi (block_length a) (update a) hash blocks
  | Blake2B | Blake2S ->
      let nb = S.length blocks / block_length a in
      let a' = to_blake_alg a in
      Lib.LoopCombinators.repeati #(words_state a) nb (Spec.Blake2.blake2_update1 a' prev blocks) hash
  | SHA3_256 ->
      let open Spec.SHA3 in
      let rateInBytes = 1088 / 8 in
      Lib.Sequence.repeat_blocks_multi #_ #(words_state a) rateInBytes blocks (absorb_inner rateInBytes) hash

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
    finish a (update_multi a (init a) () S.(input @| padding))
