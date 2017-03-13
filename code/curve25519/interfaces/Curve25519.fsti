module Curve25519
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Buffer.Quantifiers

type uint8_p = Buffer.buffer Hacl.UInt8.t

val crypto_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h mypublic /\ Buffer.live h secret /\ Buffer.live h basepoint))
    (ensures (fun h0 _ h1 -> Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1))
