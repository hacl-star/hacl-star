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


val point_inv: p: point -> result: point -> Stack unit
  (requires fun h -> live h p /\ live h result /\
    eq_or_disjoint p result /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> modifies (loc result)  h0 h1 /\  
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime /\ (
  
    let x, y, z = gsub p (size 0) (size 4),  gsub p (size 4) (size 4), gsub p (size 8) (size 4) in 
    let x3, y3, z3 = gsub result (size 0) (size 4), gsub result (size 4) (size 4), gsub result (size 8) (size 4) in 
      
    let xD, yD, zD = fromDomain_ (as_nat h0 x), fromDomain_ (as_nat h0 y), fromDomain_ (as_nat h0 z) in 
    let x3D, y3D, z3D = fromDomain_ (as_nat h1 x3), fromDomain_ (as_nat h1 y3), fromDomain_ (as_nat h1 z3) in
      
    let xN, yN, zN = _point_inverse (xD, yD, zD) in 
    x3D == xN /\ y3D == yN /\ z3D == zN)) 

