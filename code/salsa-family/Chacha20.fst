module Chacha20

open FStar.Buffer
open Hacl.Spec.Endianness
open Hacl.Impl.Chacha20

module U32 = FStar.UInt32


// JK : this is only necessary as long as the 'loop.h' hack is alive (double_round is otherwise
// killed by the bundling
val double_round:
  st:buffer Hacl.UInt32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
let double_round st = double_round st

[@ "c_inline"]
val chacha20_init_block:
  stream_block:uint8_p{length stream_block = 64} ->
  k:uint8_p{length k = 32 /\ disjoint stream_block k} ->
  n:uint8_p{length n = 12 /\ disjoint stream_block n /\ disjoint k n} ->
  Stack unit
    (requires (fun h -> live h k /\ live h n /\ live h stream_block))
    (ensures  (fun h0 log h1 -> live h1 stream_block /\ live h0 k /\ live h0 n /\ modifies_1 stream_block h0 h1
      /\ (let block = reveal_sbytes (as_seq h1 stream_block) in
              block == Spec.Chacha20.chacha20_block (as_seq h1 k) (as_seq h1 n) (U32.v 0ul))))
[@ "c_inline"]
let chacha20_init_block str k n = 
    let st = alloc () in
    let l = init st k n in
    let l = chacha20_block l str st 0ul in
    ()

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length key = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = U32.v ctr in
         o == Spec.CTR.counter_mode Spec.Chacha20.chacha20_ctx Spec.Chacha20.chacha20_cipher k n ctr plain)))
let chacha20 output plain len k n ctr = chacha20 output plain len k n ctr
