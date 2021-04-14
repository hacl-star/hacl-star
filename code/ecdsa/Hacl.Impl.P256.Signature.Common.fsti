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

val bufferToJac: #c: curve -> p: lbuffer uint64 (getCoordinateLenU64 c *. 2ul) -> result: point c -> Stack unit
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let x, y = as_nat c h0 (gsub p (size 0) len),  as_nat c h0 (gsub p len len) in
    let x3, y3, z3 = point_prime_to_coordinates c (as_seq h1 result) in 
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in 
    as_nat c h1 (gsub result (len *. size 2) len) == 1 /\ x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ))


[@ (Comment "  This code is not side channel resistant")]  
val isPointAtInfinityPublic: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec.ECC.isPointAtInfinity (point_prime_to_coordinates c (as_seq h0 p)))


[@ (Comment "  This code is not side channel resistant")]
val isPointOnCurvePublic: #c: curve -> p: point c -> Stack bool
  (requires fun h -> 
    let len = getCoordinateLenU64 c in 
    live h p /\ felem_eval c h (gsub p (size 0) len) /\ felem_eval c h (gsub p len len) /\
    as_nat c h (gsub p (size 2 *! len) len) == 1)
  (ensures fun h0 r h1 ->
    let len = getCoordinateLenU64 c in 
    modifies0 h0 h1 /\ 
    r == isPointOnCurve #c (as_nat c h1 (gsub p (size 0) len), as_nat c h1 (gsub p len len), as_nat c h1 (gsub p (size 2 *! len) len)))


[@ (Comment "  This code is not side channel resistant")] 
val verifyQValidCurvePoint: #c: curve -> pubKeyAsPoint: point c 
  -> tempBuffer:lbuffer uint64 (size 25 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKeyAsPoint /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc tempBuffer] /\ (
    let len = getCoordinateLenU64 c in as_nat c h (gsub pubKeyAsPoint (size 2 *! len) len) == 1))
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\
    ~ (isPointAtInfinity ((point_prime_to_coordinates c (as_seq h0 pubKeyAsPoint)))) /\
    r == verifyQValidCurvePointSpec #c (point_prime_to_coordinates c (as_seq h0 pubKeyAsPoint)))


val verifyQ: #c: curve -> pubKey: lbuffer uint8 (size (getPointLen c)) -> Stack bool
  (requires fun h -> live h pubKey)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size (getCoordinateLen c)))) in 
    let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size (getCoordinateLen c)) (size (getCoordinateLen c)))) in
    let pkJ = Spec.ECC.toJacobianCoordinates (publicKeyX, publicKeyY) in 
    r == verifyQValidCurvePointSpec #c pkJ))