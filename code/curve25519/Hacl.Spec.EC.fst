module Hacl.Spec.EC

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.EC.Point
open Hacl.Spec.EC.Format
open Hacl.Spec.EC.Ladder

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val crypto_scalarmult_spec:
  secret:uint8_s{Seq.length secret = 32} ->
  basepoint:uint8_s{Seq.length basepoint = 32} ->
  GTot (mypublic:uint8_s{Seq.length mypublic = 32 /\
    mypublic == Spec.Curve25519.scalarmult secret basepoint
    })
let crypto_scalarmult_spec secret basepoint =
  let q = point_of_scalar basepoint in
  let scalar = format_secret secret in
  let res = cmult_spec scalar q in
  (* cut (let r = Spec.Curve25519.Proj (Hacl.Spec.Bignum.selem (fst res)) (Hacl.Spec.Bignum.selem (snd res)) in *)
  (*   r = Spec.Curve25519.montgomery_ladder (Spec.Curve25519.decodePoint basepoint) (Spec.Curve25519.decodeScalar25519 secret)); *)
  let res = scalar_of_point res in
  res
