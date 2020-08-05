module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Spec.P256.Definition
open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication


val montgomery_multiplication_buffer_by_one: #c: curve -> a: felem c  -> result: felem c -> 
  Stack unit
    (requires (fun h -> live h a /\ as_nat c h a < getPrime c /\ live h result)) 
    (ensures (fun h0 _ h1 -> 
      let prime = getPrime c in 
      modifies (loc result) h0 h1 /\ 
      as_nat c h1 result  = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
      as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))


val montgomery_multiplication_buffer: #c: curve -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
    (requires (fun h ->
      live h a /\ as_nat c h a < getPrime c /\ live h b /\ live h result /\ as_nat c h b < getPrime c)) 
    (ensures (fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\  
      as_nat c h1 result < getPrime c /\
      as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c) /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))))


val montgomery_square_buffer: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
    (requires (fun h -> live h a /\ as_nat c h a < (getPrime c) /\ live h result)) 
    (ensures (fun h0 _ h1 -> 
      (
	let prime = getPrime c in 
	modifies (loc result) h0 h1 /\  
	as_nat c h1 result < prime /\ 
	as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
	as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
	as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))))


val exponent: #c: curve -> a: felem c -> result: felem c -> tempBuffer: lbuffer uint64 (size 20) 
  -> Stack unit
    (requires fun h -> 
      live h a /\ live h tempBuffer /\ live h result /\  disjoint tempBuffer result /\ 
      disjoint a tempBuffer /\ as_nat c h a < getPrime c)
    (ensures fun h0 _ h1 -> 
      modifies2 result tempBuffer h0 h1 /\
      (let k = fromDomain_ #c (as_nat c h0 a) in 
      as_nat c h1 result =  toDomain_ #c (pow k (getPrime c - 2) % getPrime c)))
