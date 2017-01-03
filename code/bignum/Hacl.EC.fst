module Hacl.EC

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.Format
open Hacl.EC.Ladder

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


val crypto_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h mypublic /\ Buffer.live h secret /\ Buffer.live h basepoint))
    (ensures (fun h0 _ h1 -> Buffer.live h1 mypublic /\ modifies_1 mypublic h0 h1))
let crypto_scalarmult mypublic secret basepoint =
  push_frame();  
  let q  = point_of_scalar basepoint in
  let nq = Hacl.EC.Format.point_inf () in // Storage point
  let x = getx nq in
  let z = getz nq in
  let zmone = Buffer.create limb_zero clen in
  let scalar = format_secret secret in
  cmult nq scalar q;
  scalar_of_point mypublic nq;
  pop_frame()
