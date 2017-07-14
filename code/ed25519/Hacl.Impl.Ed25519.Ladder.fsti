module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Spec.Endianness


#reset-options "--max_fuel 0 --z3rlimit 20"

val point_mul:
  result:point ->
  scalar:buffer Hacl.UInt8.t{length scalar = 32} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result /\ point_inv h q))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result
    /\ point_inv h0 q /\ live h1 result /\ modifies_1 result h0 h1 /\ point_inv h1 result /\
    (let r = as_point h1 result in
     let n  = reveal_sbytes (as_seq h0 scalar) in
     let q  = as_point h0 q in
     r == Spec.Ed25519.point_mul n q) ))
