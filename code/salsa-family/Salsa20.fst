module Salsa20

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Salsa20
open C.Loops

open Hacl.Impl.Salsa20

module Spec = Spec.Salsa20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

let value_at m (h:HyperStack.mem{live h m}) = reveal_sbytes (as_seq h m)


val salsa20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 8} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = output `value_at` h1 in
         let plain = plain `value_at` h0 in
         let k = key `value_at` h0 in
         let n = nonce `value_at` h0 in
         let ctr = UInt64.v ctr in
         o == Spec.Salsa20.salsa20_encrypt_bytes k n ctr plain)))
let salsa20 output plain len k n ctr = salsa20 output plain len k n ctr
