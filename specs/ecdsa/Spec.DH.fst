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
  -> tuple3 (lbytes (getCoordinateLen c)) (lbytes (getCoordinateLen c)) bool

let ecp256_dh_i #c s =
  let xN, yN, zN = secret_to_public #c s in
  if isPointAtInfinity #c #Jacobian (xN, yN, zN) then
    nat_to_bytes_be (getCoordinateLen c) xN, 
    nat_to_bytes_be (getCoordinateLen c) yN, 
    false
  else
    nat_to_bytes_be (getCoordinateLen c) xN, 
    nat_to_bytes_be (getCoordinateLen c) yN, 
    true


(* Responder *)
val ecp256_dh_r: #c: curve 
  -> lbytes (getCoordinateLen c) 
  -> lbytes (getCoordinateLen c) 
  -> scalar_bytes #c
  -> tuple3 (lbytes (getCoordinateLen c)) (lbytes (getCoordinateLen c)) bool

let ecp256_dh_r #c x y s =
  let x_, y_ = nat_from_bytes_be x, nat_from_bytes_be y in 
  let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates #c (x_, y_) in 
  if verifyQValidCurvePointSpec #c (pointJacX, pointJacY, pointJacZ) then 
    let xN, yN, zN = scalar_multiplication #c s (pointJacX, pointJacY, pointJacZ) in
    if isPointAtInfinity #c #Jacobian (xN, yN, zN) then
      nat_to_bytes_be (getCoordinateLen c) xN, 
      nat_to_bytes_be (getCoordinateLen c) yN, 
      false
    else
      nat_to_bytes_be (getCoordinateLen c) xN, 
      nat_to_bytes_be (getCoordinateLen c) yN, 
      true
  else
      nat_to_bytes_be (getCoordinateLen c) 0, 
      nat_to_bytes_be (getCoordinateLen c) 0, 
      false
