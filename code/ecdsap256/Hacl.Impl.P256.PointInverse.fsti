module Hacl.Impl.P256.PointInverse

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer
open Spec.P256

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication

inline_for_extraction noextract
val point_inv8: result: lbuffer uint8 (size 64) -> p: lbuffer uint8 (size 64) ->
  Stack unit 
  (requires fun h -> live h result /\ live h p /\ (
    let pX = gsub p (size 0) (size 32) in 
    let pY = gsub p (size 32) (size 32) in 
    
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pX) < prime256 /\ 
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pY) < prime256))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let open Lib.ByteSequence in 
    let pX = nat_from_bytes_be (as_seq h0 (gsub p (size 0) (size 32))) in 
    let pY = nat_from_bytes_be (as_seq h0 (gsub p (size 32) (size 32))) in
    let pK = Spec.P256.toJacobianCoordinates (pX, pY) in 
    let resultX, resultY, _ = Spec.P256._norm (Spec.P256._point_inverse pK) in 
    
    as_seq h1 (gsub result (size 0) (size 32)) == nat_to_bytes_be 32 resultX /\
    as_seq h1 (gsub result (size 32) (size 32)) == nat_to_bytes_be 32 resultY))

