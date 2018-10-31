module Spec.HMAC_Generic

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module H = Spec.Hash_Generic

val wrap_key:
    a: H.algorithm
  -> key: bytes{length key <= H.max_input a}
  -> hlen:nat{H.range_output a hlen} ->
  Tot (lbytes (H.size_block a))

val init:
    a: H.algorithm
  -> key: lbytes (H.size_block a)
  -> hlen:nat{H.range_output a hlen} ->
  Tot (H.state a)

val update_block:
    a: H.algorithm
  -> prev: nat{prev + H.size_block a <= H.max_input a}
  -> data: lbytes (H.size_block a)
  -> H.state a ->
  Tot (H.state a)

val update_last:
    a: H.algorithm
  -> prev: nat
  -> last: bytes{length last <= H.size_block a /\ length last + prev <= H.max_input a}
  -> H.state a ->
  Tot (H.state a)

val finish:
    a: H.algorithm
  -> key: lbytes (H.size_block a)
  -> H.state a
  -> hlen:nat{H.range_output a hlen} ->
  Tot (lbytes hlen)

val hmac:
    a: H.algorithm
  -> key: bytes{length key <= H.max_input a}
  -> input: bytes{length key + length input + H.size_block a <= H.max_input a}
  -> hlen: nat{H.range_output a hlen} ->
  Tot (lbytes hlen)
