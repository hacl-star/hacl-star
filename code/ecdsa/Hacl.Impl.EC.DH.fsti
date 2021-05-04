module Hacl.Impl.EC.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves
open Spec.DH
open Hacl.Spec.EC.Definition
open Hacl.Spec.ECDSA.Definition


#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel  0"

inline_for_extraction noextract
val ecp256dh_i: c: curve 
  -> result: pointAffine8 c
  -> s: scalar_t #MUT #c 
  -> Stack bool
  (requires fun h -> live h result /\ live h s /\ disjoint result s)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let pointX, pointY, flag = ecp256_dh_i #c (as_seq h0 s) in
    let x, y = as_seq h1 (getXAff8 result), as_seq h1 (getYAff8 result) in 
    pointX == x /\ pointY == y /\ r == flag))


inline_for_extraction noextract
val ecp256dh_r: #c: curve 
  -> result: pointAffine8 c
  -> pubKey: pointAffine8 c
  -> scalar: scalar_t #MUT #c 
  -> Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ disjoint result pubKey /\ disjoint result scalar)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let pubKeyX, pubKeyY = getXAff8 pubKey, getYAff8 pubKey in
    let pointX, pointY, flag = ecp256_dh_r #c (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
    let resultX, resultY = as_seq h1 (getXAff8 result), as_seq h1 (getYAff8 result) in 
    r == flag /\ resultX == pointX /\ resultY == pointY))
