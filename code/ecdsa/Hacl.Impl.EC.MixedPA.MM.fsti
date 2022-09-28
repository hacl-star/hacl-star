module Hacl.Impl.EC.MixedPA.MM

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Mul


inline_for_extraction noextract
val montgomery_multiplication_buffer_by_one_mixed: #c: curve -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h result))
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getModePrime DH c in  
    as_nat c h1 result = modp_inv2_prime (pow2 (getPower c)) prime % prime /\
    as_nat c h1 result = fromDomain_ #c #DH 1)))
