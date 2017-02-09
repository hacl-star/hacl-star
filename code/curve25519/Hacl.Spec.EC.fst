module Hacl.Spec.EC

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.EC.Point
open Hacl.Spec.EC.Format
open Hacl.Spec.EC.Ladder

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


(* val crypto_scalarmul_spec__: *)
(*   secret:uint8_s{Seq.length secret = 32} -> *)


val crypto_scalarmult_spec:
  secret:uint8_s{Seq.length secret = 32} ->
  basepoint:uint8_s{Seq.length basepoint = 32} ->
  Tot (mypublic:uint8_s{Seq.length mypublic = 32})
let crypto_scalarmult_spec secret basepoint =
  let q = point_of_scalar basepoint in
  let scalar = format_secret secret in
  let res = cmult_spec scalar q in
  scalar_of_point res
