module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module HA = Spec.Hash.Definitions
module H = Spec.Hash

val wrap_key:
    a: HA.hash_alg
  -> key:bytes{length key < HA.max_input_length a} ->
  Tot (lbytes (HA.block_length a))

(*
val init:
    a: HA.hash_alg
  -> key: lbytes (HA.block_length a) ->
  Tot (HA.words_state a)

val update_block:
    a: HA.hash_alg
  -> data: lbytes (HA.block_length a)
  -> HA.words_state a ->
  Tot (HA.words_state a)

val update_last:
    a: HA.hash_alg
  -> prev: nat{prev % HA.block_length a == 0}
  -> len: nat{len < HA.block_length a /\ len + prev < HA.max_input_length a}
  -> last: lbytes len
  -> HA.words_state a ->
  Tot (HA.words_state a)

val finish:
    a: HA.hash_alg
  -> key: lbytes (HA.block_length a)
  -> HA.words_state a ->
  Tot (lbytes (HA.hash_length a))
*)

val hmac:
    a: HA.hash_alg
  -> key:bytes{length key < HA.max_input_length a}
  -> input:bytes{length key + length input + HA.block_length a < HA.max_input_length a} ->
  Tot (lbytes (HA.hash_length a))
