module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module H = Spec.Hash.Definitions

val wrap_key:
    a: H.hash_alg
  -> key:bytes{length key < H.max_input_length a} ->
  Tot (lbytes (H.block_length a))

val init:
    a: H.hash_alg
  -> key: lbytes (H.block_length a) ->
  Tot (H.words_state a)

val update_block:
    a: H.hash_alg
  -> data: lbytes (H.block_length a)
  -> H.words_state a ->
  Tot (H.words_state a)

val update_last:
    a: H.hash_alg
  -> prev: nat{prev % H.block_length a = 0}
  -> len: nat{len < H.block_length a /\ len + prev < H.max_input_length a}
  -> last: lbytes len
  -> H.words_state a ->
  Tot (H.words_state a)

val finish:
    a: H.hash_alg
  -> key: lbytes (H.block_length a)
  -> H.words_state a ->
  Tot (lbytes (H.hash_length a))

val hmac:
    a: H.hash_alg
  -> key:bytes{length key < H.max_input_length a}
  -> input:bytes{length key + length input + H.block_length a < H.max_input_length a} ->
  Tot (lbytes (H.hash_length a))
