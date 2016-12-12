module Hacl.EC.Ladder


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.AddAndDouble


module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#set-options "--lax"

type uint8_p = buffer H8.t


val cmult_small_loop:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr ->  
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
let rec cmult_small_loop nq nqpq nq2 nqpq2 q byt i =
  let nqx = getx nq in
  let nqz = getz nq in
  let nqpqx = getx nqpq in
  let nqpqz = getz nqpq in
  let nqx2 = getx nq2 in
  let nqz2 = getz nq2 in
  let nqpqx2 = getx nqpq2 in
  let nqpqz2 = getz nqpq2 in
  if (U32.(i =^ 0ul)) then ()
  else (
    let bit = byte_to_limb (H8.(byt >>^ 7ul)) in
    swap_conditional nq nqpq bit;
    fmonty nq2 nqpq2 nq nqpq q;
    swap_conditional nq2 nqpq2 bit;
    let t = nq in
    let nq = nq2 in
    let nq2 = t in
    let t = nqpq in
    let nqpq = nqpq2 in
    let nqpq2 = t in
    let byt = H8.(byt <<^ 1ul) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byt (U32.(i -^ 1ul))
  )


val cmult_big_loop:
  n:uint8_p{length n = 32} ->
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  i:U32.t ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
let rec cmult_big_loop n nq nqpq nq2 nqpq2 q i =
  if (U32.(i =^ 0ul)) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byte 8ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 q i
  )


val cmult: result:point ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))
let cmult result n q =
  push_frame();
  let nq    = result in
  let nqpq  = Hacl.EC.Format.alloc_point () in
  let nqpq2 = Hacl.EC.Format.alloc_point () in
  let nq2   = Hacl.EC.Format.alloc_point () in
  Hacl.EC.Point.copy nqpq q;
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  copy result nq;
  pop_frame()
