module Hacl.Impl.ECDSA.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECDSA
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition

open FStar.Mul
open Hacl.Spec.MontgomeryMultiplication

#reset-options " --z3rlimit 200"

val montgomery_ladder_exponent: #c: curve -> a: felem c -> r: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h r /\ as_nat c h a < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc r) h0 h1 /\ (
    let b_ = fromDomain_ #c #DSA (as_nat c h0 a) in 
    let r0D = exponent_spec #c b_ in 
    fromDomain_ #c #DSA (as_nat c h1 r) == r0D /\
    as_nat c h1 r < getOrder #c))

val fromDomainImpl: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
     as_nat c h1 result < getOrder #c /\ as_nat c h1 result == fromDomain_ #c #DSA (as_nat c h0 a))

val multPower: #c: curve -> a: felem c -> b: felem c ->  result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat c h a < getOrder #c /\ as_nat c h b < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (pow (as_nat c h0 a) (getOrder #c - 2) * as_nat c h0 b) % getOrder #c)

val multPowerPartial: #c: curve -> s: felem c -> a: felem c 
  -> b: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h b /\ live h result /\ as_nat c h a < getOrder #c /\ as_nat c h b < getOrder #c /\ (
    let a_ = fromDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h s)) in 
    let r0D = exponent_spec #c a_ in 
    fromDomain_ #c #DSA (as_nat c h a) == r0D))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (pow (as_nat c h0 s) (getOrder #c - 2) * as_nat c h0 b) % getOrder #c)
