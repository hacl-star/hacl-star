module Hacl.Impl.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val _montgomery_ladder_power: #c: curve -> #m: mode -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getCoordinateLenU c) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getModePrime m c /\ 
    as_nat c h b < getModePrime m c /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ (
    let a_ = fromDomain_ #c #m (as_nat c h0 a) in 
    let b_ = fromDomain_ #c #m (as_nat c h0 b) in 
    let (r0D, r1D) = Lib.LoopCombinators.repeati (v (getScalarLen c)) (_pow_step #c #m (as_seq h0 scalar)) (a_, b_) in 
    r0D == fromDomain_ #c #m (as_nat c h1 a) /\ r1D == fromDomain_ #c #m (as_nat c h1 b) /\
    as_nat c h1 a < getModePrime m c /\ as_nat c h1 b < getModePrime m c))

[@CInline]
val montgomery_ladder_power: #c: curve -> #m: mode -> a: felem c 
  -> scalar: glbuffer uint8 (getCoordinateLenU c) -> result: felem c -> 
  Stack unit 
  (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getModePrime m c /\
    disjoint a scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\ 
    as_nat c h1 result < getModePrime m c /\ (
    let r0D = pow_spec #c #m (as_seq h0 scalar) (fromDomain_ #c #m (as_nat c h0 a)) in 
    let k = fromDomain_ #c #m (as_nat c h0 a) in 
    let scalar = as_seq h0 scalar in 
    let prime = getModePrime m c in 
    as_nat c h1 result = toDomain_ #c #m ((pow k (Lib.ByteSequence.nat_from_bytes_le scalar)) % prime) /\ 
    r0D == fromDomain_ #c #m (as_nat c h1 result)))
