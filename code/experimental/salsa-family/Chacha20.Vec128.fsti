module Chacha20.Vec128


open FStar.Buffer


let uint8_p = buffer Hacl.UInt8.t

#reset-options "--max_fuel 0 --z3rlimit 20"

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:UInt32.t{UInt32.v len = length output /\ UInt32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1 /\ (
      let output = as_seq h1 output in
      let key = as_seq h0 key in
      let nonce = as_seq h0 nonce in
      let ctr = UInt32.v ctr in      
      let plain = as_seq h0 plain in
      output == Spec.Chacha20_vec.chacha20_encrypt_bytes key nonce ctr plain) ))
