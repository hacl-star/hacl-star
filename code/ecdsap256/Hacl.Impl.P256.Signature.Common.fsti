module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.ByteSequence
open Lib.Buffer

open Spec.P256
open Spec.P256.Definitions

open Spec.ECDSA
open Spec.P256.Lemmas
open Spec.ECDSAP256.Definition

open Hacl.Impl.P256.Core

open FStar.Mul


val bufferToJac: p:lbuffer uint64 (size 8) -> result:point -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures  fun h0 _ h1 ->
    modifies (loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) == 1 /\
    (let x = as_nat h0 (gsub p (size 0) (size 4)) in
     let y = as_nat h0 (gsub p (size 4) (size 4)) in
     let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
     let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
     x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ))

(* This code is not side channel resistant *)
val isPointAtInfinityPublic: p:point -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == Spec.P256.isPointAtInfinity (point_prime_to_coordinates (as_seq h0 p)))

(* This code is not side channel resistant *)
(* This is unused internally and not exposed in the top-level API *)
val isPointOnCurvePublic: p:point -> Stack bool
  (requires fun h -> live h p /\    
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) == 1)
  (ensures fun h0 r h1 ->
    modifies0 h0 h1 /\ 
     r == isPointOnCurve (as_nat h1 (gsub p (size 0) (size 4)), 
                          as_nat h1 (gsub p (size 4) (size 4)), 
                          as_nat h1 (gsub p (size 8) (size 4)))
  )

(*
For Bob to authenticate Alice's signature, he must have a copy of her public-key curve point {\displaystyle Q_{A}} Q_{A}. Bob can verify {\displaystyle Q_{A}} Q_{A} is a valid curve point as follows:

Check that {\displaystyle Q_{A}} Q_{A} is not equal to the identity element {\displaystyle O} O, and its coordinates are otherwise valid
Check that {\displaystyle Q_{A}} Q_{A} lies on the curve
Check that {\displaystyle n\times Q_{A}=O}
*)

(* This code is not side channel resistant *)
val verifyQValidCurvePoint: pubKeyAsPoint:point
  -> tempBuffer:lbuffer uint64 (size 100) -> Stack bool
  (requires fun h ->
    live h pubKeyAsPoint /\
    live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc tempBuffer] /\
    point_z_as_nat h pubKeyAsPoint == 1
  )
  (ensures  fun h0 r h1 ->
    modifies (loc tempBuffer) h0 h1 /\
    r == verifyQValidCurvePointSpec (point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)))

inline_for_extraction
val verifyQ: 
  pubKey: lbuffer uint8 (size 64) ->
  Stack bool
    (requires fun h -> live h pubKey)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
      (
	let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in 
	let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
	let pkJ = Spec.P256.toJacobianCoordinates (publicKeyX, publicKeyY) in 
	r == verifyQValidCurvePointSpec pkJ
      )
    )
