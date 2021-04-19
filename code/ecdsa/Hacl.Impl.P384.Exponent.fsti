module Hacl.Impl.P384.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.MontgomeryMultiplication


val exponent_p384: a: felem P384 -> result: felem P384 -> 
  tempBuffer: lbuffer uint64 (getCoordinateLenU64 P384 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat P384 h a < getPrime P384)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let k = fromDomain_ #P384 #DH (as_nat P384 h0 a) in 
    as_nat P384 h1 result =  toDomain_ #P384 #DH (pow k (prime384 - 2) % prime384) /\
    as_nat P384 h1 result < getPrime P384)) 
