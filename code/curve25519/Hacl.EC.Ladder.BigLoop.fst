module Hacl.EC.Ladder.BigLoop


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.AddAndDouble
open Hacl.EC.Ladder.SmallLoop

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val cmult_big_loop:
  n:Buffer.buffer H8.t{length n = 32} ->
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  i:U32.t{U32.v i <= 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h n /\ frameOf n <> frameOf nq2 /\ fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq2) h0 h1
      /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let rec cmult_big_loop n nq nqpq nq2 nqpq2 q i =
  if (U32.(i =^ 0ul)) then ()
  else (
    cut (U32.v i > 0);
    let i = U32.(i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byte 8ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 q i
  )
