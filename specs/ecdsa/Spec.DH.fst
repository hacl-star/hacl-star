module Spec.DH

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.ECDSA

open Spec.ECC
open Spec.ECC.Curves

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* Initiator *)
val ecp256_dh_i: #c: curve 
  -> scalar_bytes #c
  -> tuple2 (point #c #Affine) bool

let ecp256_dh_i #c s =
  let p = secret_to_public #c s in 
  if isPointAtInfinity p then 
    (fromJacobianCoordinatesTest #c (_norm p), false)
  else
    (fromJacobianCoordinatesTest #c (_norm p), true)

(* Responder *)
val ecp256_dh_r: #c: curve 
  -> pubKey: tuple2 nat nat
  -> scalar_bytes #c
  -> tuple2 (point #c #Affine) bool

let ecp256_dh_r #c pubKey scalar  =
  let pk = toJacobianCoordinates pubKey in 
  if not (verifyQValidCurvePointSpec #c pk) then
    (0, 0), false
  else
    let pk_scalar = scalar_multiplication #c scalar pk in
    if isPointAtInfinity pk_scalar then 
      (fromJacobianCoordinatesTest #c (_norm pk_scalar), false)
    else 
      (fromJacobianCoordinatesTest #c (_norm pk_scalar), true)
