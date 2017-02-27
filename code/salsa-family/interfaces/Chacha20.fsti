module Chacha20

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open FStar.Buffer
open Hacl.Spec.Symmetric.Chacha20
open Hacl.Spec.Endianness

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t


val chacha20_key_block:
  block:uint8_p{length block = 64} ->
  k:uint8_p{length k = 32 /\ disjoint block k} ->
  n:uint8_p{length n = 12 /\ disjoint block n} ->
  ctr:UInt32.t ->
  Stack unit
    (requires (fun h -> live h block /\ live h k))
    (ensures (fun h0 _ h1 -> live h1 block /\ modifies_1 block h0 h1))

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1
      /\ live h0 key /\ live h0 nonce
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = U32.v ctr in
         o == Spec.CTR.counter_mode Spec.Chacha20.chacha20_ctx Spec.Chacha20.chacha20_cipher k n ctr plain)))
