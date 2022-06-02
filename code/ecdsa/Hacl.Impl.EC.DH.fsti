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
open Hacl.Impl.ECDSA.Setup
open Hacl.Impl.EC.Core


open Lib.ByteSequence

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel  0"

inline_for_extraction noextract
val ecp256dh_i: c: curve 
  -> l: ladder 
  -> result: pointAffine8 c
  -> scalar: scalar_t #MUT #c 
  -> Stack bool
  (requires fun h -> live h result /\ live h scalar /\ disjoint result scalar /\
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 success h1 -> modifies (loc result) h0 h1 /\  (
    let rX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let rY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    let p, flag = ecp256_dh_i #c (as_seq h0 scalar) in 
    rX < getPrime c /\ rX < getPrime c /\ flag == success /\ (
    success ==> 
      (rX, rY) == p /\ 
      ~ (isPointAtInfinity (secret_to_public (as_seq h0 scalar))) /\ 
      (rX, rY) == fromJacobianCoordinatesTest #c (_norm (secret_to_public (as_seq h0 scalar)))) /\
    (not success ==> isPointAtInfinity (secret_to_public (as_seq h0 scalar)))))


val lemma_zero_point_zero_coordinates: c: curve -> h: mem -> p: point c -> 
  Lemma (requires lseq_as_nat (as_seq h p) == 0)
  (ensures (as_nat c h (getX p) == 0) /\ (as_nat c h (getY p) == 0) /\ (as_nat c h (getZ p) == 0) /\ point_eval c h p)
    

inline_for_extraction noextract
val ecp256dh_r_public: #c: curve 
  -> #l: ladder 
  -> result: pointAffine8 c
  -> pubKey: pointAffine8 c
  -> scalar: scalar_t #MUT #c 
  -> Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ disjoint result pubKey /\ disjoint result scalar /\
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 success h1 -> modifies (loc result) h0 h1 /\  (
    let pk = nat_from_bytes_be (as_seq h0 (getXAff8 pubKey)), nat_from_bytes_be (as_seq h0 (getYAff8 pubKey)) in 
    let coordinateX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let coordinateY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    coordinateX < getPrime c /\ coordinateY < getPrime c /\ (
    let p, flag = ecp256_dh_r pk (as_seq h0 scalar) in 
    flag == success /\ 
    success ==> (coordinateX, coordinateY) == p)))


inline_for_extraction noextract
val ecp256dh_r_private: #c: curve 
  -> #l: ladder 
  -> result: pointAffine8 c
  -> pubKey: pointAffine8 c
  -> scalar: scalar_t #MUT #c 
  -> Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ disjoint result pubKey /\ disjoint result scalar /\
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 success h1 -> modifies (loc result) h0 h1 /\ (
    let pk = nat_from_bytes_be (as_seq h0 (getXAff8 pubKey)), nat_from_bytes_be (as_seq h0 (getYAff8 pubKey)) in 
    let coordinateX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let coordinateY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    coordinateX < getPrime c /\ coordinateY < getPrime c /\ (
    let p, flag = ecp256_dh_r pk (as_seq h0 scalar) in 
    flag == success /\ 
    success ==> (coordinateX, coordinateY) == p)))
