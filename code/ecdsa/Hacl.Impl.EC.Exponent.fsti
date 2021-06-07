module Hacl.Impl.EC.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.MontgomeryMultiplication

(* disjoint a result comes from ML, tempBffer - from specific *)
inline_for_extraction noextract
val exponent: #c: curve -> a: felem c -> result: felem c -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 c *. 8ul) -> 
  Stack unit
  (requires fun h -> live h a /\ live h result /\ live h tempBuffer /\ disjoint tempBuffer result /\ disjoint a tempBuffer /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> 
    let k = fromDomain #c (as_nat c h0 a) in 
    modifies (loc a |+| loc tempBuffer |+| loc result) h0 h1 /\
    as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result = toDomain_ #c #DH (pow k (getPrime c - 2) % getPrime c))

[@CInline]
val square_root: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
    as_nat c h1 result < getPrime c /\
    fromDomain #c (as_nat c h1 result) = sq_root_spec #c #DH (fromDomain #c (as_nat c h0 a)) /\
    fromDomain #c (as_nat c h1 result) = pow (fromDomain #c (as_nat c h0 a)) ((getPrime c + 1) / 4) % getPrime c)
