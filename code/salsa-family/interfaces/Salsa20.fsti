module Salsa20

open FStar.Buffer
open Hacl.Spec.Endianness
open Hacl.Endianness

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

let op_String_Access h (b:uint8_p{live h b}) = reveal_sbytes (as_seq h b)

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
      /\ (h1.[output] == Spec.Salsa20.salsa20_encrypt_bytes h0.[key] h0.[nonce] (UInt64.v ctr) h0.[plain])))

val hsalsa20:
  output:uint8_p{length output = 32} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 16} ->
  Stack unit
    (requires (fun h -> live h output /\ live h nonce /\ live h key))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 nonce /\ live h0 key /\
      modifies_1 output h0 h1 /\ live h1 output
      /\ (h1.[output] == Spec.HSalsa20.hsalsa20 h0.[key] h0.[nonce])))
