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
    (let (px, py, pz) = as_point_nat (as_seq h1 p) in
    SM.fromDomain_ px == S.g_x /\
    SM.fromDomain_ py == S.g_y /\
    SM.fromDomain_ pz == 1))


val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv (as_seq h1 p) /\
    (let (px, py, pz) = as_point_nat (as_seq h1 p) in
    SM.fromDomain_ px == 0 /\
    SM.fromDomain_ py == 0 /\
    SM.fromDomain_ pz == 0))


inline_for_extraction noextract
val copy_point: p:point -> res:point -> Stack unit
  (requires fun h -> live h p /\ live h res /\ disjoint p res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == as_seq h0 p)


///  Point conversion between Montgomery and Regular representations

val point_to_mont: p:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv (as_seq h1 res) /\
   (let px, py, pz = as_point_nat (as_seq h0 p) in
    let rx, ry, rz = as_point_nat (as_seq h1 res) in
    rx == SM.toDomain_ px /\
    ry == SM.toDomain_ py /\
    rz == SM.toDomain_ pz))


// NOT used?
val point_from_mont: p:point -> res:point-> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv (as_seq h1 res) /\
   (let px, py, pz = as_point_nat (as_seq h0 p) in
    let rx, ry, rz = as_point_nat (as_seq h1 res) in
    rx == SM.fromDomain_ px /\
    ry == SM.fromDomain_ py /\
    rz == SM.fromDomain_ pz))


///  check if a point is a point-at-infinity

// TODO: add point_inv (as_seq h p) as precondition
val is_point_at_inf: p:point -> Stack uint64
  (requires fun h ->
    live h p /\ point_z_as_nat h p < S.prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    ((uint_v r == 0 \/ uint_v r == ones_v U64) /\
    (if Spec.P256.isPointAtInfinity (SM.fromDomainPoint (as_point_nat (as_seq h0 p)))
     then uint_v r = maxint U64 else uint_v r = 0) /\
    (if Spec.P256.isPointAtInfinity (as_point_nat (as_seq h0 p))
    then uint_v r = maxint U64 else uint_v r = 0)))


// TODO: add point_inv (as_seq h p) as precondition
val is_point_at_inf_vartime: p:point -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == Spec.P256.isPointAtInfinity (as_point_nat (as_seq h0 p)))


///  Point conversion between Jacobian and Affine coordinates representations

val norm_jacob_point_x: p:point -> res:felem -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1  /\
   (let rx, _, _ = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat (as_seq h0 p))) in
    as_nat h1 res == rx))


val norm_jacob_point: p:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_point_nat (as_seq h1 res) ==
      S.norm_jacob_point (SM.fromDomainPoint (as_point_nat (as_seq h0 p))))


val to_jacob_point: p:lbuffer uint64 (size 8) -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let x = as_nat h0 (gsub p (size 0) (size 4)) in
     let y = as_nat h0 (gsub p (size 4) (size 4)) in
     as_point_nat (as_seq h1 res) == S.toJacobianCoordinates (x, y)))


///  Check if a point is on the curve

val is_point_on_curve_vartime: p:point -> Stack bool
  (requires fun h -> live h p /\
    point_inv (as_seq h p) /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_on_curve (as_point_nat (as_seq h0 p)))


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
