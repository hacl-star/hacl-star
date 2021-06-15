module Hacl.Impl.P256.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.MontgomeryMultiplication


[@ CInline]
val exponent_p256: a: felem P256 -> result: felem P256 -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 P256 *. 8ul) ->
  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat P256 h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let k = fromDomain_ #P256 #DH (as_nat P256 h0 a) in 
    as_nat P256 h1 result = toDomain_ #P256 #DH (pow k (prime256 - 2) % prime256) /\
    as_nat P256 h1 result < getPrime P256))
