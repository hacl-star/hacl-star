module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Spec.DH
open Hacl.Spec.ECDSA.Definition


inline_for_extraction noextract
val ecp256dh_i:
    c: curve 
  -> result:lbuffer uint8 (getPointLen c)
  -> scalar:lbuffer uint8 (getScalarLen c)
  -> Stack uint64
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i #c (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (getCoordinateLen c)) == pointX /\
    as_seq h1 (gsub result (getCoordinateLen c) (getCoordinateLen c)) == pointY
  )


inline_for_extraction noextract
val ecp256dh_r:
    c: curve 
  -> result:lbuffer uint8 (getPointLen c)
  -> pubKey:lbuffer uint8 (getPointLen c)
  -> scalar:lbuffer uint8 (getScalarLen c)
  -> Stack uint64
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size (getCoordinateLen c)) in
      let pubKeyY = gsub pubKey (size (getCoordinateLen c)) (size (getCoordinateLen c)) in
      let pointX, pointY, flag =
        ecp256_dh_r #c (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size (getCoordinateLen c))) == pointX /\
      as_seq h1 (gsub result (getCoordinateLen c) (getCoordinateLen c)) == pointY)
