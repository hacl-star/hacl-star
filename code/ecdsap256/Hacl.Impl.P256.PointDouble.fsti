module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Spec.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open FStar.Mul

#reset-options "--z3rlimit 300" 

val point_double: #c: curve -> p: point c -> result: point c -> tempBuffer: lbuffer uint64 (size (getCoordinateLenU64 c * 22)) -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\
    (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in
      as_nat c h (gsub p (size 0) (size len)) < prime /\ 
      as_nat c h (gsub p (size len) (size len)) < prime /\
      as_nat c h (gsub p (size (2 * len)) (size len)) < prime
    )
  )
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result)  h0 h1 /\  
    (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in 
      
      as_nat c h1 (gsub result (size 0) (size len)) < prime /\ 
      as_nat c h1 (gsub result (size len) (size len)) < prime /\
      as_nat c h1 (gsub result (size (2 * len)) (size len)) < prime /\ 
      
      (
	let x, y, z = gsub p (size 0) (size len), gsub p (size len) (size len), gsub p (size (2 * len)) (size len) in 
	let x3, y3, z3 = gsub result (size 0) (size len), gsub result (size len) (size len), gsub result (size (2 * len)) (size len) in 
      
	let xD, yD, zD = fromDomain_ (as_nat c h0 x), fromDomain_ (as_nat c h0 y), fromDomain_ (as_nat c h0 z) in 
	let x3D, y3D, z3D = fromDomain_ (as_nat c h1 x3), fromDomain_ (as_nat c h1 y3), fromDomain_ (as_nat c h1 z3) in
	let xN, yN, zN = _point_double #c (xD, yD, zD) in 
	x3D == xN /\ y3D == yN /\ z3D == zN
      )
    ) 
  )
