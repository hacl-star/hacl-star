module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition

open Spec.ECDSA
open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

val bufferToJac: #c: curve -> p: pointAffine c -> result: point c -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\ felem_eval c h (getXAff p) /\ felem_eval c h (getYAff p))
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
    let x, y = as_nat c h0 (getXAff p), as_nat c h0 (getYAff p) in 
    let resultTuple = point_as_nat c h1 result in 
    let pJ = toJacobianCoordinates (x, y) in 
    ~ (isPointAtInfinity resultTuple) /\ as_nat c h1 (getZ result) == 1 /\ resultTuple == pJ))


[@ (Comment "  This code is not side channel resistant")]  
val isPointAtInfinityPublic: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec.ECC.isPointAtInfinity (point_prime_to_coordinates c (as_seq h0 p)))


[@ (Comment "  This code is not side channel resistant")]
val isPointOnCurvePublic: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p /\ felem_eval c h (getX p) /\ felem_eval c h (getY p) /\ as_nat c h (getZ p) == 1)
  (ensures fun h0 r h1 ->  modifies0 h0 h1 /\ r == isPointOnCurve #c (point_as_nat c h0 p))


[@ (Comment "  This code is not side channel resistant")] 
val verifyQValidCurvePoint: #c: curve -> pubKey: point c 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ point_eval c h pubKey /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat c h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (let p = point_as_nat c h0 pubKey in 
    ~ (isPointAtInfinity p) /\ r == verifyQValidCurvePointSpec #c p))


val verifyQ: #c: curve -> pubKey: pointAffine8 c -> Stack bool
  (requires fun h -> live h pubKey)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h1 (getXAff8 pubKey)) in 
    let publicKeyY = nat_from_bytes_be (as_seq h1 (getYAff8 pubKey)) in
    let pkJ = Spec.ECC.toJacobianCoordinates (publicKeyX, publicKeyY) in 
    r == verifyQValidCurvePointSpec #c pkJ))
