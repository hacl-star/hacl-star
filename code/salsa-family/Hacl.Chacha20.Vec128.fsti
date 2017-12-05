module Hacl.Chacha20.Vec128

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Buffer
open FStar.UInt32

let uint8_p = buffer Hacl.UInt8.t

#reset-options "--max_fuel 0 --z3rlimit 20"

private let op_String_Access h (b:uint8_p{live h b}) = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

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
      /\ modifies_1 output h0 h1 /\
      h1.[output] == Spec.Chacha20.chacha20_encrypt_bytes h0.[key] h0.[nonce] (v ctr) h0.[plain] ))
