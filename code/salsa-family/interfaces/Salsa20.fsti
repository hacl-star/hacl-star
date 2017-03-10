module Salsa20

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open FStar.Buffer

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t


val crypto_stream_salsa20_xor_ic:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 8} ->
  ic:FStar.UInt64.t ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))

val crypto_stream_salsa20:
  c:uint8_p ->
  clen:FStar.UInt64.t{U64.v clen <= length c} ->
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))

val crypto_stream_salsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
