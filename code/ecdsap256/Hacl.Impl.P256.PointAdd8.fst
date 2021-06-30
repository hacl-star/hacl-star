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

friend Hacl.Impl.P256.Core

#set-options "--z3rlimit 150 --ifuel 0 --fuel 0" 

val _point_add8: p: point -> q: point -> result: point -> tempBuffer: lbuffer uint64 (size 88) -> 
  Stack unit (requires fun h -> live h p /\ live h q /\ live h result /\ live h tempBuffer /\
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime /\
    as_nat h (gsub q (size 0) (size 4)) < prime /\ 
    as_nat h (gsub q (size 4) (size 4)) < prime /\  
    as_nat h (gsub q (size 8) (size 4)) < prime ) 
   (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc result |+| loc tempBuffer) h0 h1 /\
     as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
     as_nat h1 (gsub result (size 4) (size 4)) < prime /\  
     as_nat h1 (gsub result (size 8) (size 4)) < prime /\ (
     let pxD, pyD, pzD = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
     let qxD, qyD, qzD = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in 
     Spec.P256._norm (Spec.P256._point_add (pxD, pyD, pzD) (qxD, qyD, qzD)) =  Spec.P256.point_prime_to_coordinates (as_seq h1 result)))


let _point_add8 p q result tempBuffer = 
  pointToDomain p p;
  pointToDomain q q;
  point_add p q result tempBuffer;
  norm result result tempBuffer
