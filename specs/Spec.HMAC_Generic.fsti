module Spec.HMAC_Generic

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module H = Spec.Hash_Generic

val wrap_key:
    a: H.algorithm
  -> len: size_nat{len < H.max_input a}
  -> key: lbytes len
  -> hlen:nat{H.range_output a hlen} ->
  Tot (lbytes (H.size_block a))

val init:
    a: H.algorithm
  -> key: lbytes (H.size_block a)
  -> hlen:nat{H.range_output a hlen} ->
  Tot (H.state a)

val update_block:
    a: H.algorithm
  -> prev:nat{prev + H.size_block a <= H.max_input a}
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
  -> H.state a
  -> hlen:nat{H.range_output a hlen} ->
  Tot (lbytes hlen)

val hmac:
    a: H.algorithm
  -> klen: size_nat{klen < H.max_input a}
  -> key:lbytes klen
  -> len:size_nat{klen + len + H.size_block a <= H.max_input a}
  -> input:lbytes len
  -> hlen:nat{H.range_output a hlen} ->
  Tot (lbytes hlen)
