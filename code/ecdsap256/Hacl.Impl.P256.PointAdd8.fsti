module Hacl.Impl.P256.PointAdd8

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointAdd
open FStar.Mul

open Hacl.Impl.P256.Core
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel

inline_for_extraction noextract
val point_add8: result: lbuffer uint8 (size 64) -> p: lbuffer uint8 (size 64) -> q: lbuffer uint8 (size 64) -> 
  Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h q /\ (
    let pX = gsub p (size 0) (size 32) in 
    let pY = gsub p (size 32) (size 32) in 
    let qX = gsub q (size 0) (size 32) in 
    let qY = gsub q (size 32) (size 32) in
    
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pX) < prime256 /\ 
    Lib.ByteSequence.nat_from_bytes_be (as_seq h pY) < prime256 /\
    Lib.ByteSequence.nat_from_bytes_be (as_seq h qX) < prime256 /\
    Lib.ByteSequence.nat_from_bytes_be (as_seq h qY) < prime256))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let open Lib.ByteSequence in 
    let pX = nat_from_bytes_be (as_seq h0 (gsub p (size 0) (size 32))) in 
    let pY = nat_from_bytes_be (as_seq h0 (gsub p (size 32) (size 32))) in
    let pK = Spec.P256.toJacobianCoordinates (pX, pY) in 
    
    let qX = nat_from_bytes_be (as_seq h0 (gsub q (size 0) (size 32))) in 
    let qY = nat_from_bytes_be (as_seq h0 (gsub q (size 32) (size 32))) in
    let qK = Spec.P256.toJacobianCoordinates (qX, qY) in 
    let resultX, resultY, _ = Spec.P256._norm (Spec.P256._point_add pK qK) in 
    
    as_seq h1 (gsub result (size 0) (size 32)) == nat_to_bytes_be 32 resultX /\
    as_seq h1 (gsub result (size 32) (size 32)) == nat_to_bytes_be 32 resultY))

