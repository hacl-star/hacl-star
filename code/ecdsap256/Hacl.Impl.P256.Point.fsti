module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.ByteSequence
open Lib.Buffer

open Spec.P256
open Spec.P256.Constants
open Spec.P256.MontgomeryMultiplication
open Spec.ECDSA

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Core

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

noextract
let point_x_as_nat (h: mem) (e: point) : GTot nat =
  let open Lib.Sequence in
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)

noextract
let point_y_as_nat (h: mem) (e: point) : GTot nat =
  let open Lib.Sequence in
  let s = as_seq h e in
  let s0 = s.[4] in
  let s1 = s.[5] in
  let s2 = s.[6] in
  let s3 = s.[7] in
  as_nat4 (s0, s1, s2, s3)

noextract
let point_z_as_nat (h: mem) (e: point) : GTot nat =
  let open Lib.Sequence in
  let s = as_seq h e in
  let s0 = s.[8] in
  let s1 = s.[9] in
  let s2 = s.[10] in
  let s3 = s.[11] in
  as_nat4 (s0, s1, s2, s3)


val uploadBasePoint: p: point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    as_nat h1 (gsub p (size 0) (size 4)) < prime256 /\
    as_nat h1 (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub p (size 8) (size 4)) < prime256 /\
      (
	let x1 = as_nat h1 (gsub p (size 0) (size 4)) in
	let y1 = as_nat h1 (gsub p (size 4) (size 4)) in
	let z1 = as_nat h1 (gsub p (size 8) (size 4)) in

	let bpX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 in
	let bpY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 in

	fromDomain_ x1 == bpX /\ fromDomain_ y1 == bpY /\ fromDomain_ z1 ==  1
    )
)


val zero_buffer: p: point ->
  Stack unit
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 ->
      modifies (loc p) h0 h1 /\
      (
	let k = Lib.Sequence.create 12 (u64 0) in
	as_nat h1 (gsub p (size 0) (size 4)) == 0 /\
	as_nat h1 (gsub p (size 4) (size 4)) == 0 /\
	as_nat h1 (gsub p (size 8) (size 4)) == 0
    )
  )


val copy_point: p: point -> result: point -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_seq h1 result == as_seq h0 p)


val isPointAtInfinityPrivate: p: point -> Stack uint64
  (requires fun h -> live h p /\ as_nat h (gsub p (size 8) (size 4)) < prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (
      (uint_v r == 0 \/ uint_v r == maxint U64) /\
      (
	let x, y, z = fromDomainPoint(point_prime_to_coordinates (as_seq h0 p)) in
	if Spec.P256.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0
      ) /\
      (
	let x, y, z = point_prime_to_coordinates (as_seq h0 p) in
	if Spec.P256.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0
      )
   )
  )

val pointToDomain: p: point -> result: point -> Stack unit
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\
    point_x_as_nat h p < prime /\ point_y_as_nat h p < prime /\ point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
    point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
    point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p))


val pointFromDomain: p: point -> result: point-> Stack unit
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\
  point_x_as_nat h p < prime /\ point_y_as_nat h p < prime /\ point_z_as_nat h p < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    point_x_as_nat h1 result == fromDomain_ (point_x_as_nat h0 p) /\
    point_y_as_nat h1 result == fromDomain_ (point_y_as_nat h0 p) /\
    point_z_as_nat h1 result == fromDomain_ (point_z_as_nat h0 p))


val norm: p: point -> resultPoint: point -> tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h resultPoint /\ live h tempBuffer /\ disjoint p tempBuffer /\ disjoint tempBuffer resultPoint /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
  )
  (ensures fun h0 _ h1 ->
      modifies (loc tempBuffer |+| loc resultPoint) h0 h1 /\
      (
      let resultPoint =  point_prime_to_coordinates (as_seq h1 resultPoint) in
      let pointD = fromDomainPoint (point_prime_to_coordinates (as_seq h0 p)) in
      let pointNorm = _norm pointD in
      pointNorm == resultPoint
   )
  )


val normX: p: point -> result: felem -> tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc result; loc tempBuffer] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
  )
  (ensures fun h0 _ h1 ->
      modifies (loc tempBuffer |+| loc result) h0 h1  /\
      (
	let pxD = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in
	let pyD = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in
	let pzD = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in

	let (xN, _, _) = _norm (pxD, pyD, pzD) in
	as_nat h1 result == xN
      )
  )



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
val verifyQValidCurvePoint: pubKeyAsPoint:point -> Stack bool
  (requires fun h ->
    live h pubKeyAsPoint /\
    point_z_as_nat h pubKeyAsPoint == 1
  )
  (ensures  fun h0 r h1 ->
    modifies0 h0 h1 /\
    r == verifyQValidCurvePointSpec (point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)))


// TODO: mv
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


// TODO: mv
val isMoreThanZeroLessThanOrder: x: lbuffer uint8 (size 32) -> Stack bool
  (requires fun h -> live h x)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (
      let scalar = nat_from_bytes_be (as_seq h0 x) in
      r <==> (scalar > 0 && scalar < prime_p256_order)
    )
  )
