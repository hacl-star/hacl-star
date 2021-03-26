module Hacl.Impl.ECDSA.MM.Exponent


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

(* open FStar.Math.Lemmas *)

(* open Spec.ECC.Lemmas *)
open Hacl.Spec.ECDSA.Definition
open Spec.ECDSA
open Hacl.Impl.P256.LowLevel 
open Spec.ECC
open Spec.ECC.Curves

(* open Spec.ECC.Lemmas *)

open FStar.Mul

open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Lib.Loops

#reset-options " --z3rlimit 200"

noextract
let prime = getOrder #P256

val montgomery_ladder_exponent: #c: curve -> a: felem c -> Stack unit 
  (requires fun h -> live h a /\ as_nat c h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    (
      let b_ = fromDomain_ (as_nat c h0 a) in 
      let r0D = exponent_spec #P256 b_ in 
      fromDomain_ (as_nat c h1 a) == r0D  /\
      as_nat c h1 a < prime
    )
)

val fromDomainImpl: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
     as_nat c h1 result < prime /\ as_nat c h1 result == fromDomain_ (as_nat c h0 a))

val multPower: #c: curve -> a: felem c -> b: felem c ->  result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat c h a < prime /\ as_nat c h b < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (pow (as_nat c h0 a) ((getOrder #P256) - 2)  * (as_nat c h0 b)) % prime)


val multPowerPartial: #c: curve -> s: felem c -> a: felem c 
  -> b: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat c h a < prime /\ as_nat c h b < prime /\ 
  (
      let a_ = fromDomain_  (fromDomain_ (as_nat c h s)) in 
      let r0D = exponent_spec #P256 a_ in 
      fromDomain_ (as_nat c h a) == r0D)
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (pow (as_nat c h0 s) (prime - 2)  * (as_nat c h0 b)) % prime)
