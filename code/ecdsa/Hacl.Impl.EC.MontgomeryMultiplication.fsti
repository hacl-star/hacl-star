module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.P256.Definition
open Spec.P256

open FStar.Mul

val montgomery_multiplication_buffer_by_one: #c: curve
  -> a: felem c
  -> result: felem c -> 
  Stack unit
    (requires (fun h -> live h a /\ felem_eval c h a /\ live h result)) 
    (ensures (fun h0 _ h1 -> 
      let prime = getPrime c in 
      modifies (loc result) h0 h1 /\ 
      as_nat c h1 result = (as_nat c h0 a * modp_inv2_prime (getPower2 c) prime) % prime /\
      as_nat c h1 result = fromDomain_ #c (as_nat c h0 a)))


val montgomery_multiplication_buffer: #c: curve 
  -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
    (requires (fun h ->
      live h a /\ live h b /\ live h result /\ felem_eval c h a  /\ felem_eval c h b)) 
    (ensures (fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\  
      felem_eval c h1 result /\
      as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c) /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))))


val montgomery_square_buffer: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
    (requires (fun h -> live h a /\ felem_eval c h a /\ live h result)) 
    (ensures (fun h0 _ h1 -> 
      (
  let prime = getPrime c in 
  modifies (loc result) h0 h1 /\  
  felem_eval c h1 result /\ 
  as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
  as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
  as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))))





val fsquarePowN: #c: curve -> n: size_t -> a: felem c -> Stack unit 
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c)) 
  (ensures (fun h0 _ h1 -> (*
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in
    modifies (loc a) h0 h1 /\ as_nat P256 h1 a < prime256 /\ 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 (v n)))*) True))
