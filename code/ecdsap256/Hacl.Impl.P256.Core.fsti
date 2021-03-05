module Hacl.Impl.P256.Core

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer


open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointAdd

open Spec.P256

open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer
open FStar.Mul

inline_for_extraction noextract 
val toDomain: value: felem -> result: felem ->  Stack unit 
  (requires fun h ->  as_nat h value < prime /\ live h value /\live h result /\ eq_or_disjoint value result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = toDomain_ (as_nat h0 value))
 
 
inline_for_extraction noextract
val fromDomain: f: felem-> result: felem-> Stack unit 
  (requires fun h -> live h f /\ live h result /\ as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = (as_nat h0 f * modp_inv2(pow2 256)) % prime /\ 
    as_nat h1 result = fromDomain_ (as_nat h0 f))


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



inline_for_extraction noextract
val scalarMultiplication: #buf_type: buftype->  p: point -> result: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> 
    modifies3 p result tempBuffer h0 h1 /\ 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    as_nat h1 (gsub result (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime256 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 


val scalarMultiplicationWithoutNorm: p: point -> result: point -> 
  scalar: lbuffer  uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ 
    
    as_nat h1 (gsub result (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime256 /\
    
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let p1 = fromDomainPoint(point_prime_to_coordinates (as_seq h1 result)) in 
      let rN, _ = montgomery_ladder_spec (as_seq h0 scalar) ((0, 0, 0),  point_prime_to_coordinates (as_seq h0 p)) in 
      rN == p1
  )
) 


val secretToPublic: result: point -> scalar: lbuffer uint8 (size 32) -> tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h result /\ live h scalar /\ live h tempBuffer /\ 
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result]
    )
  (
    ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = secret_to_public (as_seq h0 scalar)  in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    )
  )

val secretToPublicWithoutNorm: result: point -> scalar: lbuffer uint8 (size 32) -> 
 tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h result /\ live h scalar /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result]
    )
  (
    ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
      as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
      as_nat h1 (gsub result (size 4) (size 4)) < prime /\ 
      as_nat h1 (gsub result (size 8) (size 4)) < prime /\
      (
	let p1 = fromDomainPoint(point_prime_to_coordinates (as_seq h1 result)) in 
	let rN, _ = montgomery_ladder_spec (as_seq h0 scalar) ((0, 0, 0), basePoint) in 
	rN == p1))  
