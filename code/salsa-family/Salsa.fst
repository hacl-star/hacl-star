module Salsa

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Salsa20
open Combinators

open Hacl.Impl.Salsa20

module Spec = Spec.Salsa20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

#reset-options "--initial_fuel 0 --max_fuel 0"

val double_round:
  st:buffer H32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == Spec.double_round s)))
[@ "c_inline"]
let double_round st = double_round st

val salsa20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length key = 12} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = UInt64.v ctr in
         o == Spec.CTR.counter_mode Spec.salsa20_ctx Spec.salsa20_cipher k n ctr plain)))
let salsa20 output plain len k n ctr = salsa20 output plain len k n ctr
