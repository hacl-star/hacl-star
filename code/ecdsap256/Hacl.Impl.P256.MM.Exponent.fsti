module Hacl.Impl.P256.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.P256.Math 

open Hacl.Impl.P256.LowLevel 
open FStar.Tactics
open FStar.Tactics.Canon 

open FStar.Mul

open Lib.Loops

open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Arithmetics

open Hacl.Spec.P256.Definition
(* open Spec.P256.Lemmas *)
open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication

inline_for_extraction noextract
val square_root: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
    as_nat c h1 result < prime256 /\
    fromDomain_ #c (as_nat c h1 result) = sq_root_spec (fromDomain_ #c (as_nat c h0 a)) /\
    fromDomain_ #c (as_nat c h1 result) = pow (fromDomain_ #c (as_nat c h0 a)) ((prime256 + 1) / 4) % prime256
  )
