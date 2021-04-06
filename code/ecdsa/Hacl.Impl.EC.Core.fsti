module Hacl.Impl.EC.Core

open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication

open Spec.ECC
open Spec.ECC.Curves
open FStar.Mul


#set-options "--z3rlimit 100" 

inline_for_extraction noextract 
val toDomain: #c: curve -> value: felem c -> result: felem c -> Stack unit 
  (requires fun h -> felem_eval c h value /\ live h value /\ live h result /\ eq_or_disjoint value result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = toDomain #c (as_nat c h0 value) /\ 
    felem_eval c h1 result)
 
inline_for_extraction noextract
val fromDomain: #c: curve -> f: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h f /\ live h result /\ felem_eval c h f)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (as_nat c h0 f * modp_inv2 #c (pow2 (getPower c))) % getPrime c /\ 
    as_nat c h1 result = fromDomain #c (as_nat c h0 f))

val pointToDomain: #c: curve -> p: point c -> result: point c -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\
    point_x_as_nat c h1 result == toDomain_ #c #DH (point_x_as_nat c h0 p) /\
    point_y_as_nat c h1 result == toDomain_ #c #DH (point_y_as_nat c h0 p) /\
    point_z_as_nat c h1 result == toDomain_ #c #DH (point_z_as_nat c h0 p))

val pointFromDomain: #c : curve -> p: point c -> result: point c-> Stack unit 
  (requires fun h -> live h p /\ live h result /\ eq_or_disjoint p result /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\
    point_x_as_nat c h1 result == fromDomain_ #c #DH (point_x_as_nat c h0 p) /\
    point_y_as_nat c h1 result == fromDomain_ #c #DH (point_y_as_nat c h0 p) /\
    point_z_as_nat c h1 result == fromDomain_ #c #DH (point_z_as_nat c h0 p))
    
val isPointAtInfinityPrivate: #c: curve -> p: point c -> Stack uint64
  (requires fun h -> live h p /\ felem_eval c h (getZ p))
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ ((uint_v r == 0 \/ uint_v r == maxint U64) /\ (
    let xD, yD, zD = fromDomainPoint #c #DH (point_prime_to_coordinates c (as_seq h0 p)) in 
    let x, y, z = point_prime_to_coordinates c (as_seq h0 p) in 
    if Spec.ECC.isPointAtInfinity (xD, yD, zD) then uint_v r = maxint U64 else uint_v r = 0 /\ (
    if Spec.ECC.isPointAtInfinity (x, y, z) then uint_v r = maxint U64 else uint_v r = 0))))

val norm: #c: curve -> p: point c -> resultPoint: point c -> 
  tempBuffer: lbuffer uint64 (size 22 *! getCoordinateLenU64 c) -> Stack unit
  (requires fun h -> live h p /\ live h resultPoint /\ live h tempBuffer /\ point_eval c h p /\
    disjoint p tempBuffer /\ disjoint tempBuffer resultPoint) 
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc resultPoint) h0 h1 /\ (
    let resultPoint = point_prime_to_coordinates c (as_seq h1 resultPoint) in 
    let pointD = fromDomainPoint #c #DH (point_prime_to_coordinates c (as_seq h0 p)) in 
    let pointNorm = _norm #c pointD in
    pointNorm == resultPoint))

val normX: #c: curve -> p: point c -> result: felem c -> tempBuffer: lbuffer uint64 (size 22 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc result; loc tempBuffer] /\ point_eval c h p) 
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ (
    let pxD = fromDomain_ #c #DH (point_x_as_nat c h0 p) in 
    let pyD = fromDomain_ #c #DH (point_y_as_nat c h0 p) in 
    let pzD = fromDomain_ #c #DH (point_z_as_nat c h0 p) in 
    let (xN, _, _) = _norm #c (pxD, pyD, pzD) in 
    as_nat c h1 result == xN))


inline_for_extraction noextract
val scalarMultiplication: #c: curve -> #buf_type: buftype 
  -> p: point c
  -> result: point c 
  -> scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c)
  -> tempBuffer: lbuffer uint64 (size 25 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\ point_eval c h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_prime_to_coordinates c (as_seq h p))))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h0 p /\ point_eval c h1 result /\ (
    let r = point_prime_to_coordinates c (as_seq h1 result) in
    let rN = scalar_multiplication #c (as_seq h0 scalar) (point_prime_to_coordinates c (as_seq h0 p)) in 
    r == rN))


val scalarMultiplicationWithoutNorm: #c: curve 
  -> p: point c 
  -> result: point c 
  -> scalar: lbuffer uint8 (getScalarLenBytes c) 
  -> tempBuffer: lbuffer uint64 (size 25 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> point_eval c h p /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_prime_to_coordinates c (as_seq h p))))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p1 = fromDomainPoint #c #DH (point_prime_to_coordinates c (as_seq h1 result)) in 
    let p = point_prime_to_coordinates c (as_seq h0 p) in point_mult_0 #c p 0; 
    let rN, _ = montgomery_ladder_spec_left #c (as_seq h0 scalar) (pointAtInfinity, p) in 
    rN == p1)) 
    

val secretToPublic: #c: curve -> result: point c 
  -> scalar: lbuffer uint8 (getScalarLenBytes c) 
  -> tempBuffer: lbuffer uint64 (size 25 *! getCoordinateLenU64 c) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval c h0 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p = point_prime_to_coordinates c (as_seq h1 result) in 
    let r = secret_to_public #c (as_seq h0 scalar) in 
    p == r))

val secretToPublicWithoutNorm: #c: curve -> result: point c 
  -> scalar: lbuffer uint8 (getScalarLenBytes c) 
  -> tempBuffer: lbuffer uint64 (size 25 *! getCoordinateLenU64 c) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval c h0 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p1 = fromDomainPoint #c #DH (point_prime_to_coordinates c (as_seq h1 result)) in 
    point_mult_0 (basePoint #c) 0;
    let rN, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, basePoint #c) in 
    rN == p1))  
