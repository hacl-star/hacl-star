module Spec.Agile.Hash

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish

let init a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.init a
  | MD5 ->
      Spec.MD5.init
  | SHA1 ->
      Spec.SHA1.init

let update a =
  match a with
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
      Spec.SHA2.update a
  | MD5 ->
      Spec.MD5.update
  | SHA1 ->
      Spec.SHA1.update

let update_multi
  (a:hash_alg)
  (hash:words_state a)
  (blocks:bytes_blocks a)
=
  Lib.UpdateMulti.mk_update_multi (block_length a) (update a) hash blocks

(* As defined in the NIST standard; pad, then update, then finish. *)
let hash (a:hash_alg) (input:bytes{S.length input <= max_input_length a})
  =
  let padding = pad a (S.length input) in
  finish a (update_multi a (init a) S.(input @| padding))
