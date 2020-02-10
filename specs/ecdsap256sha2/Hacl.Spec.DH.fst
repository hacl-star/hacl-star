module Hacl.Spec.DH

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence
open Lib.Sequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Spec.P256
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSA

#set-options "--fuel 0 --ifuel 0 --z3rlimit 300"
(* the code for initiator of DH key exchange *)

val ecp256_dh_i: s: lbytes 32 -> Tot (r: tuple3 (lbytes 32) (lbytes 32) uint64)

let ecp256_dh_i s = 
  let xN, yN, zN = secret_to_public s in 
  if isPointAtInfinity (xN, yN, zN) then 
    nat_to_bytes_be #SEC 32 xN, nat_to_bytes_be #SEC 32 yN, u64 (pow2 64 - 1)
  else 
    nat_to_bytes_be #SEC 32 xN, nat_to_bytes_be #SEC 32 yN, (u64 0)

(* the code for repondeur of DH key exchange *)


val ecp256_dh_r: x: lbytes 32 -> y: lbytes 32 -> s: lbytes 32 -> Tot (tuple3 (lbytes 32) (lbytes 32) uint64)

let ecp256_dh_r x y s = 
  let x_, y_ = nat_from_bytes_be x, nat_from_bytes_be y in 
  let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x_, y_) in 
  if not (verifyQValidCurvePointSpec (pointJacX, pointJacY, pointJacZ)) then 
    nat_to_bytes_be #SEC 32 0, nat_to_bytes_be #SEC 32 0, u64 (pow2 64 - 1)
  else
    let xN, yN, zN = scalar_multiplication s (pointJacX, pointJacY, pointJacZ) in 
    if isPointAtInfinity (xN, yN, zN) then
      nat_to_bytes_be #SEC 32 xN, nat_to_bytes_be #SEC 32 yN, u64 (pow2 64 - 1)
    else 
      nat_to_bytes_be #SEC 32 xN, nat_to_bytes_be #SEC 32 yN, u64 0
