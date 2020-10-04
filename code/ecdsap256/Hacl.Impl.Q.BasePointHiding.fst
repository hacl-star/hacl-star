module Hacl.Impl.Q.BasePointHiding


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel

open Spec.P256
open Spec.P256.Definitions

open FStar.Mul


open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Lib.Loops

open Lib.IntTypes.Intrinsics

open Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Core



(* usually p -> toDomain -> ... -> fromDomain -> r *)

val basePointRandomisation: p: point -> resultPoint: point -> 
  Stack unit 
    (requires fun h -> live h p /\ live h resultPoint)
    (ensures fun h0 _ h1 -> 
      let resultPoint = point_prime_to_coordinates (as_seq h1 resultPoint) in 
      let resultFromDomain = fromDomainPoint resultPoint in 
      let pointOriginal = point_prime_to_coordinates (as_seq h0 p) in 
      let resultNormalized = _norm resultFromDomain in 
      pointOriginal == resultNormalized)
      
(* or this, depends *)
      
(*
val basePointRandomisation: p: point -> resultPoint: point -> 
  Stack unit 
    (requires fun h -> live h p /\ live h resultPoint)
    (ensures fun h0 _ h1 -> 
      let resultPoint = point_prime_to_coordinates (as_seq h1 resultPoint) in 
      let pointOriginal = point_prime_to_coordinates (as_seq h0 p) in 
      let resultNormalized = _norm resultPoint in 
      pointOriginal == resultNormalized)
*)


let basePointRandomisation p result = 
  admit()
