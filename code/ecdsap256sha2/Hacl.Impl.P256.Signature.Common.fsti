module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer 
open Lib.ByteSequence
open Lib.Buffer 

open Hacl.Spec.P256 
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSA
open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256

open Hacl.Math
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.P256.Arithmetics

let prime = prime256

(* This code is not side channel resistant *)
(* inline_for_extraction noextract *)
val eq_u64_nCT:a:uint64 -> b:uint64 -> Tot (r: bool {if uint_v a = uint_v b then r == true else r == false})

(* This code is not side channel resistant *)
(* inline_for_extraction noextract *)
val eq_0_u64: a: uint64 -> Tot (r: bool {if uint_v a = 0 then r == true else r == false})

val changeEndian: i: felem -> Stack unit 
  (requires fun h -> live h i)
  (ensures fun h0 _ h1 -> modifies1 i h0 h1 /\ as_seq h1 i == Hacl.Spec.ECDSA.changeEndian (as_seq h0 i)) 

val toUint64ChangeEndian: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be #_ #_ #4 (as_seq h0 i))
  )

val lemma_core_0: a: lbuffer uint64 (size 4) -> h: mem -> Lemma (nat_from_intseq_le (as_seq h a) == as_nat h a)

val lemma_core_1: a: lbuffer uint64 (size 4) -> h: mem -> 
  Lemma (nat_from_bytes_le (Lib.ByteSequence.uints_to_bytes_le (as_seq h a)) == as_nat h a)

val bufferToJac: p: lbuffer uint64 (size 8) -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\ as_nat h1 (gsub result (size 8) (size 4)) == 1 /\ 
    (
      let x = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y = as_nat h0 (gsub p (size 4) (size 4)) in 
      let x3, y3, z3 = point_x_as_nat h1 result,  point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in 
      x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ
    )
  )   

inline_for_extraction noextract
val upload_p256_point_on_curve_constant: x: felem -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies (loc x) h0 h1 /\ 
    as_nat h1 x == toDomain_ (41058363725152142129326129780047268409114441015993725554835256314039467401291) /\
    as_nat h1 x < prime
 )


(* This code is not side channel resistant *)
val isPointAtInfinityPublic: p: point -> Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    (
      let x, y, z = point_prime_to_coordinates (as_seq h0 p) in 
      r == Hacl.Spec.P256.isPointAtInfinity (x, y, z)
    )
  ) 


(* This code is not side channel resistant *)
(* This is unused internally and not exposed in the top-level API *)
val isPointOnCurvePublic: p: point -> Stack bool
  (requires fun h -> live h p /\    
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) == 1)

  (ensures fun h0 r h1 ->      
    modifies0 h0 h1 /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let x_ = as_nat h0 x in  
      if r = false 
  then (as_nat h0 y) * (as_nat h0 y) % prime <>  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime
       else (as_nat h0 y) * (as_nat h0 y) % prime == (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime) /\
      r == isPointOnCurve (
      as_nat h1 (gsub p (size 0) (size 4)), as_nat h1 (gsub p (size 4) (size 4)), as_nat h1 (gsub p (size 8) (size 4))
  ) 
)


val isCoordinateValid: p: point -> Stack bool 
  (requires fun h -> live h p /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 -> 
    modifies0 h0 h1  /\ 
    (
      if (point_x_as_nat h0 p < prime256 && point_y_as_nat h0 p < prime256 && point_z_as_nat h0 p < prime256) then r == true else r == false
    )  
  )          

(* This code is not side channel resistant *) 
(* Checks whether the base point * order is point at infinity *)
val isOrderCorrect: p: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack bool
  (requires fun h -> 
    live h p /\ live h tempBuffer /\ 
    disjoint p tempBuffer /\
    point_x_as_nat h p < prime256 /\ 
    point_y_as_nat h p < prime256 /\
    point_z_as_nat h p < prime256
  )
  (ensures fun h0 r h1 -> 
    modifies(loc tempBuffer) h0 h1 /\ 
    (
      let (xN, yN, zN) = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      if Hacl.Spec.P256.isPointAtInfinity (xN, yN, zN) then r == true else r == false
    )
  )  

(*
For Bob to authenticate Alice's signature, he must have a copy of her public-key curve point {\displaystyle Q_{A}} Q_{A}. Bob can verify {\displaystyle Q_{A}} Q_{A} is a valid curve point as follows:

Check that {\displaystyle Q_{A}} Q_{A} is not equal to the identity element {\displaystyle O} O, and its coordinates are otherwise valid
Check that {\displaystyle Q_{A}} Q_{A} lies on the curve
Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O
*)

(* This code is not side channel resistant *) 
val verifyQValidCurvePoint: pubKeyAsPoint: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack bool
  (requires fun h -> 
    live h pubKeyAsPoint /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc tempBuffer] /\
    point_z_as_nat h pubKeyAsPoint == 1
  )
  (ensures fun h0 r h1 -> 
    modifies (loc tempBuffer) h0 h1 /\ 
    r == verifyQValidCurvePointSpec (point_prime_to_coordinates (as_seq h0 pubKeyAsPoint))
  )   
