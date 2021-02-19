
module Hacl.Impl.EC.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.P256
open Spec.ECDSA.Lemmas

open Hacl.Impl.EC.LowLevel

open Lib.Loops
open Hacl.Spec.P.MontgomeryMultiplication

open Hacl.Impl.P256.MontgomeryMultiplication.Exponent
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.MM.Exponent

open FStar.Mul


val exponent: #c: curve -> a: felem c -> result: felem c -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 c *. 8ul) 
  -> Stack unit
    (requires fun h -> 
      live h a /\ live h result /\ as_nat c h a < getPrime c)
    (ensures fun h0 _ h1 -> 
      let k = fromDomain_ #c (as_nat c h0 a) in 
      modifies (loc a |+| loc result) h0 h1 /\
      as_nat c h1 result = toDomain_ #c (pow k (getPrime c - 2) % getPrime c))


val square_root: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
    as_nat c h1 result < getPrime c /\
    fromDomain_ #c (as_nat c h1 result) = sq_root_spec #c (fromDomain_ #c (as_nat c h0 a)) /\
    fromDomain_ #c (as_nat c h1 result) = pow (fromDomain_ #c (as_nat c h0 a)) ((getPrime c + 1) / 4) % getPrime c
  )
