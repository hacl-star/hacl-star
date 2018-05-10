module Hacl.SecureAPI.Chacha20

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open Hacl.Lib.LoadStore32
open Hacl.Impl.Chacha20


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ Substitute]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:UInt32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let setup st k n c = setup st k n c

[@ Substitute]
val chacha20_core:
  k:state ->
  st:state{disjoint st k} ->
  Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h0 st /\ live h0 k
      /\ live h1 k /\ live h1 st /\ modifies_1 k h0 h1))
[@ Substitute]
let chacha20_core k st =
  copy_state k st;
  rounds k;
  sum_states k st


[@ Substitute]
val chacha20_stream:
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))
[@ Substitute]
let chacha20_stream stream_block st =
  push_frame();
  let h_0 = ST.get() in
  let st' = Buffer.create (Hacl.Cast.uint32_to_sint32 0ul) 16ul in
  let log' = chacha20_core st' st in
  uint32s_to_le_bytes stream_block st' 16ul;
  let h = ST.get() in
  cut (modifies_2_1 stream_block h_0 h);
  pop_frame()


[@ Substitute]
val chacha20_stream_finish:
  stream_block:uint8_p ->
  len:UInt32.t{UInt32.v len <= 64 /\ length stream_block = UInt32.v len} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ live h0 st
      /\ live h1 st /\ live h0 stream_block /\ modifies_1 stream_block h0 h1))
[@ Substitute]
let chacha20_stream_finish stream_block len st =
  push_frame();
  let b = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  chacha20_stream b st;
  blit b 0ul stream_block 0ul len;
  pop_frame()
