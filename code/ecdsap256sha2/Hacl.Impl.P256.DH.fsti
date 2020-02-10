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
open Hacl.Spec.DH

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
      let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in 
      let resultX = as_seq h1 (gsub result (size 0) (size 32)) in 
      let resultY = as_seq h1 (gsub result (size 32) (size 32)) in  
      r == flag /\ pointX == resultX /\ pointY == resultY
    )  
  )

(* This code is not constant-time on pubKey *)
val ecp256dh_r: result: lbuffer uint8 (size 64) -> pubKey: lbuffer uint8 (size 64) -> scalar: lbuffer uint8 (size 32) -> 
  Stack uint64
    (requires fun h -> 
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar /\ disjoint pubKey scalar /\
      Lib.ByteSequence.nat_from_bytes_le #SEC (as_seq h (gsub result (size 0) (size 32))) == 0 /\ 
      Lib.ByteSequence.nat_from_bytes_le #SEC (as_seq h (gsub result (size 32) (size 32))) == 0 /\ 
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) >= 1 /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) < Hacl.Spec.ECDSAP256.Definition.prime_p256_order)
    (ensures fun h0 r h1 -> 
      modifies (loc result) h0 h1 /\ 
	(
	  let pubKeyX, pubKeyY = gsub pubKey (size 0) (size 32), gsub pubKey (size 32) (size 32) in
	  let pointX, pointY, flag = ecp256_dh_r (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in 
	  let resultX = as_seq h1 (gsub result (size 0) (size 32)) in 
	  let resultY = as_seq h1 (gsub result (size 32) (size 32)) in  
	  r == flag /\ pointX == resultX /\ pointY == resultY
	)
    )
