module Hacl.EC.Ladder.BigLoop

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.EC.Point
open Hacl.EC.Point
open Hacl.EC.AddAndDouble
open Hacl.EC.Ladder.SmallLoop
open Hacl.Spec.EC.Ladder

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
      /\ Buffer.live h0 n
      /\ HyperStack.modifies_one (frameOf nq2) h0 h1
      /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q
      /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq), (as_seq h1 (getz nq))) in
         let spointb1 : spoint_513 = (as_seq h1 (getx nqpq), (as_seq h1 (getz nqpq))) in
         let pointq   : spoint_513' = (as_seq h0 (getx q), (as_seq h0 (getz q))) in
         let spointa0 : spoint_513 = (as_seq h0 (getx nq), (as_seq h0 (getz nq))) in
         let spointb0 : spoint_513 = (as_seq h0 (getx nqpq), (as_seq h0 (getz nqpq))) in
         (spointa1) == cmult_big_loop_spec (as_seq h0 n) (spointa0) (spointb0) pointq i)
    ))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 1000"

 let rec cmult_big_loop n nq nqpq nq2 nqpq2 q i =
 if (U32.(i =^ 0ul)) then ()
 else (
    cut (U32.v i > 0);
    let i = U32.(i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byte 4ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 q i
    )
