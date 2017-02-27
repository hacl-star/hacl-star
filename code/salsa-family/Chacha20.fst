module Chacha20

open FStar.Buffer
open Hacl.Spec.Endianness
open Hacl.Impl.Chacha20

module U32 = FStar.UInt32

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val chacha20_key_block:
  block:uint8_p{length block = 64} ->
  k:uint8_p{length k = 32 /\ disjoint block k} ->
  n:uint8_p{length n = 12 /\ disjoint block n} ->
  ctr:UInt32.t ->
  Stack unit
    (requires (fun h -> live h block /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h1 block /\ modifies_1 block h0 h1))
let chacha20_key_block block k n ctr =
  push_frame();
  let st = alloc () in
  let l  = init st k n in
  let l  = chacha20_block l block st ctr in
  pop_frame()


// JK : this is only necessary as long as the 'loop.h' hack is alive (double_round is otherwise
// killed by the bundling
val double_round:
  st:buffer Hacl.UInt32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
let double_round st = double_round st


let value_at m (h:HyperStack.mem{live h m}) = reveal_sbytes (as_seq h m)


val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h nonce /\ live h key))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1
      /\ live h0 nonce /\ live h0 key
      /\ (let o = output `value_at` h1 in
         let plain = plain `value_at` h0 in
         let k = key `value_at` h0 in
         let n = nonce `value_at` h0 in
         let ctr = U32.v ctr in
         o == Spec.Chacha20.chacha20_encrypt_bytes k n ctr plain)))
let chacha20 output plain len k n ctr = chacha20 output plain len k n ctr
