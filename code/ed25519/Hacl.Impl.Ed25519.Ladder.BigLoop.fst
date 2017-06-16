//
//   Copyright 2016-2017  INRIA
//
//   Maintainers: Jean-Karim Zinzindohoué
//                Karthikeyan Bhargavan
//                Benjamin Beurdouche
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//

module Hacl.Impl.Ed25519.Ladder.BigLoop


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.UInt64
open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.SmallLoop

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val cmult_big_loop:
  n:Buffer.buffer H8.t{length n = 32} ->
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  i:U32.t{U32.v i <= 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h n /\ frameOf n <> frameOf nq2 (* /\ fmonty_pre h nq2 nqpq2 nq nqpq q *)))
    (ensures (fun h0 _ h1 -> (* fmonty_pre h0 nq2 nqpq2 nq nqpq q *)
      (* /\  *)Buffer.live h0 n
      /\ HyperStack.modifies_one (frameOf nq2) h0 h1
      (* /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q *)
      (* /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq), (as_seq h1 (getz nq))) in *)
      (*    let spointb1 : spoint_513 = (as_seq h1 (getx nqpq), (as_seq h1 (getz nqpq))) in *)
      (*    let pointq   : spoint_513' = (as_seq h0 (getx q), (as_seq h0 (getz q))) in *)
      (*    let spointa0 : spoint_513 = (as_seq h0 (getx nq), (as_seq h0 (getz nq))) in *)
      (*    let spointb0 : spoint_513 = (as_seq h0 (getx nqpq), (as_seq h0 (getz nqpq))) in *)
      (*    (spointa1) == cmult_big_loop_spec (as_seq h0 n) (spointa0) (spointb0) pointq i) *)
    ))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 1000"
let rec cmult_big_loop n nq nqpq nq2 nqpq2 i =
  if (U32.(i =^ 0ul)) then ()
  else (
    cut (U32.v i > 0);
    let i = U32.(i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 byte 4ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 i
  )
