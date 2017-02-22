module Chacha

open FStar.Buffer
open Hacl.Impl.Chacha20

module U32 = FStar.UInt32

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length key = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain
      /\ modifies_1 output h0 h1))
      (* /\ (let o = as_seq h1 output in *)
      (*    let plain = as_seq h0 plain in *)
      (*    o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) plain))) *)
let chacha20 output plain len k n ctr = chacha20 output plain len k n ctr
