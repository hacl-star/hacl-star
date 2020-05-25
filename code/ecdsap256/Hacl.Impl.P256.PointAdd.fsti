module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Impl.SolinasReduction
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open Hacl.Impl.P256.PointDouble

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

open FStar.Mul

#reset-options "--z3rlimit 300" 


val point_add: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> 
   Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
   eq_or_disjoint q result /\
   disjoint p q /\ disjoint p tempBuffer /\ disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime 
    ) 
   (ensures fun h0 _ h1 -> 
     modifies (loc tempBuffer |+| loc result) h0 h1 /\ 
     as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 4) (size 4)) < prime /\
     (
       let pX, pY, pZ = gsub p (size 0) (size 4), gsub p (size 4) (size 4), gsub p (size 8) (size 4) in 
       let qX, qY, qZ = gsub q (size 0) (size 4), gsub q (size 4) (size 4), gsub q (size 8) (size 4) in 
       let x3, y3, z3 = gsub result (size 0) (size 4), gsub result (size 4) (size 4), gsub result (size 8) (size 4) in 
       
       let pxD, pyD, pzD = fromDomain_ (as_nat h0 pX), fromDomain_ (as_nat h0 pY), fromDomain_ (as_nat h0 pZ) in 
       let qxD, qyD, qzD = fromDomain_ (as_nat h0 qX), fromDomain_ (as_nat h0 qY), fromDomain_ (as_nat h0 qZ) in 
       let x3D, y3D, z3D = fromDomain_ (as_nat h1 x3), fromDomain_ (as_nat h1 y3), fromDomain_ (as_nat h1 z3) in
      
       let xN, yN, zN = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in 
       x3D == xN /\ y3D == yN /\ z3D == zN
  )
)
