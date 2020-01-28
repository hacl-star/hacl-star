module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2

open Hacl.Spec.P256
open Hacl.Spec.ECDSA
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256
open Hacl.Impl.P256.Signature.Common

val ecp256dh_i: result: lbuffer uint8 (size 64) -> scalar: lbuffer uint8 (size 32) -> Stack uint64
  (requires fun h -> live h result /\ live h scalar /\ disjoint result scalar /\
    Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) >= 1 /\
    Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) < Hacl.Spec.ECDSAP256.Definition.prime_p256_order
  )
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\
    (
      let xN, yN, zN = secret_to_public (as_seq h0 scalar) in 
      let resultX = gsub result (size 0) (size 32) in 
      let resultY = gsub result (size 32) (size 32) in 
      if isPointAtInfinity (xN, yN, zN) then uint_v r = maxint U64 else uint_v r = 0 /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h1 resultX) == xN /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h1 resultY) == yN
    )  
  )


val ecp256dh_r: result: lbuffer uint8 (size 64) -> pubKey: lbuffer uint8 (size 64) -> scalar: lbuffer uint8 (size 32) -> 
  Stack uint64
    (requires fun h -> 
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar /\ disjoint pubKey scalar /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) >= 1 /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) < Hacl.Spec.ECDSAP256.Definition.prime_p256_order)
    (ensures fun h0 flag h1 -> 
      modifies (loc result) h0 h1 /\ 
	(
	  let pubKeyX, pubKeyY = gsub pubKey (size 0) (size 32), gsub pubKey (size 32) (size 32) in 
	  let x, y = nat_from_bytes_le (as_seq h0 pubKeyX), nat_from_bytes_le (as_seq h0 pubKeyY) in 
	  let resultX, resultY = gsub result (size 0) (size 32), gsub result (size 32) (size 32) in 
	  let x3, y3 = nat_from_bytes_le (as_seq h1 resultX), nat_from_bytes_le (as_seq h1 resultY) in 
	  let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in 
	  if not (verifyQValidCurvePointSpec (pointJacX, pointJacY, pointJacZ)) then 
	    uint_v flag = maxint U64
	  else 
	    let xN, yN, zN = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in 
	    xN == x3 /\ yN == y3 /\
	    (
	      if isPointAtInfinity (xN, yN, zN) then 
		uint_v flag = maxint U64
	      else 
		uint_v flag = 0
	    )
	)
    )
