module Hacl.Poly1305_64

open FStar.HyperStack.All
open FStar.Mul
open FStar.Endianness
open FStar.Buffer
open FStar.UInt64

open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 100"

(* Type Aliases *)
let uint8_p = Buffer.buffer Hacl.UInt8.t
let uint64_t = FStar.UInt64.t
private let op_String_Access h (b:uint8_p{live h b}) = reveal_sbytes (as_seq h b)


val crypto_onetimeauth:
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64_t{v len < pow2 32 /\ v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\
      live h0 input /\ live h0 key /\
      h1.[mac] == Spec.Poly1305.poly1305 h0.[input] h0.[key]))
