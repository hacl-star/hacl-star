module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.Core

open Spec.ECDSA
open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
val bufferToJac: #c: curve -> p: pointAffine c -> result: point c -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\ 
    felem_eval c h (getXAff p) /\ felem_eval c h (getYAff p) /\
    ~ (isPointAtInfinity #Affine (point_affine_as_nat c h p)))
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
    let x, y = as_nat c h0 (getXAff p), as_nat c h0 (getYAff p) in 
    let resultTuple = point_as_nat c h1 result in 
    let pJ = toJacobianCoordinates (x, y) in 
    ~ (isPointAtInfinity #Jacobian resultTuple) /\ as_nat c h1 (getZ result) == 1 /\ resultTuple == pJ))

inline_for_extraction noextract
val fromForm: #c: curve -> i: felem c -> o: coordinateAffine8 c -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ as_nat c h i < pow2 (getPower c))
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\  
    as_seq h1 o == nat_to_bytes_be (v (getCoordinateLenU c)) (as_nat c h0 i) /\ 
    nat_from_bytes_be (as_seq h1 o) == as_nat c h0 i)


inline_for_extraction noextract
val fromFormPoint: #c: curve -> i: point c -> o: pointAffine8 c -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ point_eval c h i /\ (
    let xCoordinate, yCoordinate, _ = point_as_nat c h i in 
    xCoordinate < pow2 (getPower c) /\ yCoordinate < pow2 (getPower c)))
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\ (
    let coordinateX_u64, coordinateY_u64, _ = point_as_nat c h0 i in 
    let coordinateX_u8, coordinateY_u8 = getXAff8 #c o, getYAff8 #c o in
    as_seq h1 (coordinateX_u8) == nat_to_bytes_be (getCoordinateLen c) coordinateX_u64 /\
    as_seq h1 (coordinateY_u8) == nat_to_bytes_be (getCoordinateLen c) coordinateY_u64 /\ 
    nat_from_bytes_be (as_seq h1 (coordinateX_u8)) == coordinateX_u64 /\
    nat_from_bytes_be (as_seq h1 (coordinateY_u8)) == coordinateY_u64))


inline_for_extraction noextract
val toForm: #c: curve -> i: coordinateAffine8 c -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_nat c h1 o == nat_from_bytes_be (as_seq h0 i))

inline_for_extraction noextract
val toFormPoint: #c: curve -> i: pointAffine8 c -> o: point c -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 i)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 i)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0))
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h0 (getXAff8 i))  in 
    let pointScalarYSeq = nat_from_bytes_be (as_seq h0 (getYAff8 i)) in 
    let x, y, z = as_nat c h1 (getX o), as_nat c h1 (getY o), as_nat c h1 (getZ o) in  
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (pointScalarXSeq, pointScalarYSeq) in 
    x == pointScalarXSeq /\ y == pointScalarYSeq /\ z == 1 /\
    x == pointJacX /\ y == pointJacY /\ z == pointJacZ))


inline_for_extraction noextract
val isPointAtInfinity_public: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p /\ point_eval c h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec.ECC.isPointAtInfinity #Jacobian (point_as_nat c h0 p))


inline_for_extraction noextract
val isPointOnCurve: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p /\ felem_eval c h (getX p) /\ felem_eval c h (getY p) /\ as_nat c h (getZ p) == 1)
  (ensures fun h0 r h1 ->  modifies0 h0 h1 /\ r == isPointOnCurve #c (point_as_nat c h0 p))


inline_for_extraction noextract
val verifyQValidCurvePoint_private: #c: curve -> #l: ladder -> pubKey: point c 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat c h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let p = as_nat c h0 (getX pubKey),  as_nat c h0 (getY pubKey),  as_nat c h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #c p))


inline_for_extraction noextract
val verifyQValidCurvePoint_public: #c: curve -> #l: ladder -> pubKey: point c 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat c h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let p = as_nat c h0 (getX pubKey),  as_nat c h0 (getY pubKey),  as_nat c h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #c p))


inline_for_extraction noextract
val verifyQ_public: #c: curve -> #l: ladder -> pubKey: pointAffine8 c -> Stack bool
  (requires fun h -> live h pubKey  /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 pubKey)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 pubKey)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h1 (getXAff8 pubKey)) in 
    let publicKeyY = nat_from_bytes_be (as_seq h1 (getYAff8 pubKey)) in
    let pkJ = Spec.ECC.toJacobianCoordinates (publicKeyX, publicKeyY) in 
    r == verifyQValidCurvePointSpec #c pkJ))


inline_for_extraction noextract
val verifyQ_private: #c: curve -> #l: ladder -> pubKey: pointAffine8 c -> Stack bool
  (requires fun h -> live h pubKey /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 pubKey)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 pubKey)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h1 (getXAff8 pubKey)) in 
    let publicKeyY = nat_from_bytes_be (as_seq h1 (getYAff8 pubKey)) in
    let pkJ = Spec.ECC.toJacobianCoordinates (publicKeyX, publicKeyY) in 
    r == verifyQValidCurvePointSpec #c pkJ))
