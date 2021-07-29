module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.ByteSequence
open Lib.Buffer

open Spec.P256
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem

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

inline_for_extraction noextract
val bufferToJacUpdate: result: point -> Stack unit
  (requires fun h -> live h result)
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) == 1 /\ (
    let x = as_nat h0 (gsub result (size 0) (size 4)) in
    let y = as_nat h0 (gsub result (size 4) (size 4)) in
    let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
    x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ))



[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")] 
val isPointAtInfinityPublic: p:point -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == Spec.P256.isPointAtInfinity (point_prime_to_coordinates (as_seq h0 p)))

[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")] 
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


[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")] 
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

val isMoreThanZeroLessThanOrder: x: lbuffer uint8 (size 32) -> Stack bool
  (requires fun h -> live h x)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (
      let scalar = nat_from_bytes_be (as_seq h0 x) in 
      r <==> (scalar > 0 && scalar < prime_p256_order)
    )
  )



inline_for_extraction noextract
val toForm: i: lbuffer uint8 (size 32) -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ Lib.ByteSequence.nat_from_bytes_be (as_seq h i) < prime256)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_nat h1 o == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 i) /\
    as_nat h1 o < prime)


inline_for_extraction noextract
val toFormPoint: p: lbuffer uint8 (size 64) -> o: point -> Stack unit 
  (requires fun h -> live h p /\ live h o /\ disjoint p o /\ (
    let pX = gsub p (size 0) (size 32) in 
    let pY = gsub p (size 32) (size 32) in 
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pX) < prime256 /\
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pY) < prime256))
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ (
    let pX, pY = gsub p (size 0) (size 32), gsub p (size 32) (size 32) in
    let rX, rY, rZ = gsub o (size 0) (size 4),  gsub o (size 4) (size 4), gsub o (size 8) (size 4) in 

    as_nat h1 rX == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pX) /\
    as_nat h1 rY == Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pY) /\

    (as_nat h1 rX, as_nat h1 rY, as_nat h1 rZ) == 
      Spec.P256.toJacobianCoordinates (Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pX), Lib.ByteSequence.nat_from_bytes_be (as_seq h0 pY)) /\
    as_nat h1 rX < prime /\ as_nat h1 rY < prime /\ as_nat h1 rZ == 1))


inline_for_extraction noextract
val fromForm: i: felem -> o: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ as_nat h i < prime256)
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\  
    as_seq h1 o == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 i))


inline_for_extraction noextract
val fromFormPoint: i: point -> o: lbuffer uint8 (size 64) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ (
    let iX = gsub i (size 0) (size 4) in 
    let iY = gsub i (size 4) (size 4) in 
    as_nat h iX < prime256 /\ as_nat h iY < prime256))
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\ (
    let iX = gsub i (size 0) (size 4) in 
    let iY = gsub i (size 4) (size 4) in 

    let oX = gsub o (size 0) (size 32) in 
    let oY = gsub o (size 32) (size 32) in 

    as_seq h1 oX == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 iX) /\ 
    as_seq h1 oY == Lib.ByteSequence.nat_to_bytes_be 32 (as_nat h0 iY)))
