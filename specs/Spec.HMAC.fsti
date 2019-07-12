module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module H = Spec.Hash

val wrap_key:
    a: H.algorithm
  -> key:bytes{length key <= H.max_input a} ->
  Tot (lbytes (H.size_block a))

val init:
    a: H.algorithm
  -> key: lbytes (H.size_block a) ->
  Tot (H.state a)

val update_block:
    a: H.algorithm
  -> data: lbytes (H.size_block a)
  -> H.state a ->
  Tot (H.state a)

val update_last:
    a: H.algorithm
  -> prev: nat
  -> len: nat{len < H.size_block a /\ len + prev <= H.max_input a}
  -> last: lbytes len
  -> H.state a ->
  Tot (H.state a)

val finish:
    a: H.algorithm
  -> key: lbytes (H.size_block a)
  -> H.state a ->
  Tot (lbytes (H.size_hash a))

val hmac:
    a: H.algorithm
  -> key:bytes{length key <= H.max_input a}
  -> input:bytes{length key + length input + H.size_block a <= H.max_input a} ->
  Tot (lbytes (H.size_hash a))
