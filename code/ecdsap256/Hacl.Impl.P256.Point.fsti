module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.P256
module SD = Spec.ECDSA
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let point_seq = LSeq.lseq uint64 12

let as_point_nat (p:point_seq) =
  felem_seq_as_nat (LSeq.sub p 0 4),
  felem_seq_as_nat (LSeq.sub p 4 4),
  felem_seq_as_nat (LSeq.sub p 8 4)

let point_inv (p:point_seq) =
  let x, y, z = as_point_nat p in
  x < S.prime /\ y < S.prime /\ z < S.prime

// TODO: rename
let point_prime = p:point_seq{point_inv p}

inline_for_extraction noextract
let point = lbuffer uint64 (size 12)

noextract
let point_x_as_nat (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e 0ul 4ul)

noextract
let point_y_as_nat (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e 4ul 4ul)

noextract
let point_z_as_nat (h: mem) (e: point) : GTot nat =
  as_nat h (gsub e 8ul 4ul)

inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 4ul /\ h0 == h1)
  = sub p 0ul 4ul

inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 4ul 4ul /\ h0 == h1)
  = sub p 4ul 4ul

inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 8ul 4ul /\ h0 == h1)
  = sub p 8ul 4ul



val make_base_point: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv (as_seq h1 p) /\
    (let (x1, y1, z1) = as_point_nat (as_seq h1 p) in
    SM.fromDomain_ x1 == S.g_x /\
    SM.fromDomain_ y1 == S.g_y /\
    SM.fromDomain_ z1 == 1))


val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv (as_seq h1 p) /\
    (let (x1, y1, z1) = as_point_nat (as_seq h1 p) in
    SM.fromDomain_ x1 == 0 /\
    SM.fromDomain_ y1 == 0 /\
    SM.fromDomain_ z1 == 0))


val copy_point: p:point -> res:point -> Stack unit
  (requires fun h -> live h p /\ live h res /\ disjoint p res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == as_seq h0 p)


///  check if a point is a point-at-infinity

val isPointAtInfinityPrivate: p:point -> Stack uint64
  (requires fun h ->
    live h p /\ as_nat h (gsub p (size 8) (size 4)) < S.prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    ((uint_v r == 0 \/ uint_v r == maxint U64) /\
    (let x, y, z = SM.fromDomainPoint (as_point_nat (as_seq h0 p)) in
     if Spec.P256.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0) /\
     (let x, y, z = as_point_nat (as_seq h0 p) in
     if Spec.P256.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0)))


[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val isPointAtInfinityPublic: p:point -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == Spec.P256.isPointAtInfinity (as_point_nat (as_seq h0 p)))


///  Point conversion between Montgomery and Regular representations

val point_to_mont: p:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv (as_seq h1 res) /\
   (let x0, y0, z0 = as_point_nat (as_seq h0 p) in
    let x1, y1, z1 = as_point_nat (as_seq h1 res) in
    x1 == SM.toDomain_ x0 /\
    y1 == SM.toDomain_ y0 /\
    z1 == SM.toDomain_ z0))


val point_from_mont: p:point -> res:point-> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv (as_seq h1 res) /\
   (let x0, y0, z0 = as_point_nat (as_seq h0 p) in
    let x1, y1, z1 = as_point_nat (as_seq h1 res) in
    x1 == SM.fromDomain_ x0 /\
    y1 == SM.fromDomain_ y0 /\
    z1 == SM.fromDomain_ z0))


///  Point conversion between Jacobian and Affine coordinates representations

val norm:
    p:point
  -> resultPoint:point
  -> tempBuffer:lbuffer uint64 (size 88) ->
  Stack unit
  (requires fun h ->
    live h p /\ live h resultPoint /\ live h tempBuffer /\
    disjoint p tempBuffer /\ disjoint tempBuffer resultPoint /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime)
  (ensures fun h0 _ h1 ->
    modifies (loc tempBuffer |+| loc resultPoint) h0 h1 /\
    (let resultPoint = as_point_nat (as_seq h1 resultPoint) in
    let pointD = SM.fromDomainPoint (as_point_nat (as_seq h0 p)) in
    let pointNorm = S.norm_jacob_point pointD in
    pointNorm == resultPoint))


val normX:
    p:point
  -> result:felem
  -> tempBuffer:lbuffer uint64 (size 88) ->
  Stack unit
  (requires fun h ->
    live h p /\ live h result /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc result; loc tempBuffer] /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime)
  (ensures fun h0 _ h1 ->
    modifies (loc tempBuffer |+| loc result) h0 h1  /\
    (let pxD = SM.fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in
    let pyD = SM.fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in
    let pzD = SM.fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in
    let (xN, _, _) = S.norm_jacob_point (pxD, pyD, pzD) in
    as_nat h1 result == xN))


val bufferToJac: p:lbuffer uint64 (size 8) -> result:point -> Stack unit
  (requires fun h ->
    live h p /\ live h result /\ disjoint p result)
  (ensures  fun h0 _ h1 ->
    modifies (loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) == 1 /\
    (let x = as_nat h0 (gsub p (size 0) (size 4)) in
     let y = as_nat h0 (gsub p (size 4) (size 4)) in
     let x3, y3, z3 =
       point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
     let pointJacX, pointJacY, pointJacZ = S.toJacobianCoordinates (x, y) in
     x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ))

///  Check if a point is on the curve

[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val isPointOnCurvePublic: p:point -> Stack bool
  (requires fun h -> live h p /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) == 1)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_on_curve (as_nat h1 (gsub p (size 0) (size 4)),
                        as_nat h1 (gsub p (size 4) (size 4)),
                        as_nat h1 (gsub p (size 8) (size 4))))



[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val verifyQValidCurvePoint: pubKeyAsPoint:point -> Stack bool
  (requires fun h ->
    live h pubKeyAsPoint /\
    point_z_as_nat h pubKeyAsPoint == 1)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == SD.verifyQValidCurvePointSpec (as_point_nat (as_seq h0 pubKeyAsPoint)))


// TODO: mv
inline_for_extraction
val verifyQ: pubKey:lbuffer uint8 (size 64) -> Stack bool
  (requires fun h -> live h pubKey)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let publicKeyX = BSeq.nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
    let publicKeyY = BSeq.nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
    let pkJ = Spec.P256.toJacobianCoordinates (publicKeyX, publicKeyY) in
    r == SD.verifyQValidCurvePointSpec pkJ))


// TODO: mv
val isMoreThanZeroLessThanOrder: x:lbuffer uint8 (size 32) -> Stack bool
  (requires fun h -> live h x)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let scalar = BSeq.nat_from_bytes_be (as_seq h0 x) in
    r <==> (scalar > 0 && scalar < S.order)))
