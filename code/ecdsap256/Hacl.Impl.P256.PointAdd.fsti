module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

(* open Spec.P256.Lemmas *)
open Hacl.Spec.P256.Definition
open Spec.P256
open Hacl.Impl.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P.LowLevel 
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open Hacl.Impl.P256.PointDouble

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

open FStar.Mul

#set-options "--z3rlimit 100"

val point_add: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 22 *! getCoordinateLenU64 c) -> 
   Stack unit (requires fun h -> 
     live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
     eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
     disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in 
      
      as_nat c h (gsub p (size 0) len) < prime /\ 
      as_nat c h (gsub p len len) < prime /\ 
      as_nat c h (gsub p (size 2 *! len) len) < prime /\
      
      as_nat c h (gsub q (size 0) len) < prime /\ 
      as_nat c h (gsub q len len) < prime /\ 
      as_nat c h (gsub q (size 2 *! len) len) < prime
      )
   )
   (ensures fun h0 _ h1 -> 
     modifies (loc tempBuffer |+| loc result) h0 h1 /\ 
     (
       let len : size_t = getCoordinateLenU64 c in 
       let prime = getPrime c in 
     
       as_nat c h1 (gsub result (size 0) len) < prime /\ 
       as_nat c h1 (gsub result len len) < prime /\ 
       as_nat c h1 (gsub result (2ul *! len) len) < prime /\
       
       (
       let pX, pY, pZ = gsub p (size 0) len, gsub p len len, gsub p (size 2 *! len) len in 
       let qX, qY, qZ = gsub q (size 0) len, gsub q len len, gsub q (size 2 *! len) len in 
       let x3, y3, z3 = gsub result (size 0) len, gsub result len len, gsub result (size 2 *! len) len in 
       
       let pxD, pyD, pzD = fromDomain_ #c (as_nat c h0 pX), fromDomain_ #c (as_nat c h0 pY), fromDomain_ #c (as_nat c h0 pZ) in 
       let qxD, qyD, qzD = fromDomain_ #c (as_nat c h0 qX), fromDomain_ #c (as_nat c h0 qY), fromDomain_ #c (as_nat c h0 qZ) in 
       let x3D, y3D, z3D = fromDomain_ #c (as_nat c h1 x3), fromDomain_ #c (as_nat c h1 y3), fromDomain_ #c (as_nat c h1 z3) in
      
       let xN, yN, zN = _point_add #c (pxD, pyD, pzD) (qxD, qyD, qzD) in 
       x3D == xN /\ y3D == yN /\ z3D == zN
   )
   )
   )
