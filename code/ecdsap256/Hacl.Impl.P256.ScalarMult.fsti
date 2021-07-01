module Hacl.Impl.P256.ScalarMult

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Spec.ECDSA
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Core

open Spec.DH


inline_for_extraction noextract
val verifyQPrivate: 
  pubKey: lbuffer uint8 (size 64) ->
  Stack bool
  (requires fun h -> live h pubKey)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in 
    let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
    let pkJ = Spec.P256.toJacobianCoordinates (publicKeyX, publicKeyY) in 
    r == not (verifyQValidCurvePointSpec pkJ)))

inline_for_extraction noextract
val ecp256scalar_mult:
    result:lbuffer uint8 (size 64)
  -> pubKey:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 32) in
      let pubKeyY = gsub pubKey (size 32) (size 32) in
      let pointX, pointY, flag =
        ecp256_dh_r (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub result (size 32) (size 32)) == pointY)
