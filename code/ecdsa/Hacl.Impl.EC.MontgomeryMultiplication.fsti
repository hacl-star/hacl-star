module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.P256.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Mul


val montgomery_multiplication_reduction: #c: curve
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ wide_as_nat c h t < getPrime c * pow2 (getPower c) /\ live h result /\ 
    eq_or_disjoint t result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result |+| loc t) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (wide_as_nat c h0 t))))

val montgomery_multiplication_buffer_by_one: #c: curve -> a: felem c -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ felem_eval c h a /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getPrime c in 
    as_nat c h1 result = (as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c (as_nat c h0 a))))

val montgomery_multiplication_buffer: #c: curve -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h result /\ felem_eval c h a /\ felem_eval c h b)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ felem_eval c h1 result /\
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))))

val montgomery_square_buffer: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ felem_eval c h a /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ felem_eval c h1 result /\
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a))))


val fsquarePowN: #c: curve -> n: size_t -> a: felem c -> Stack unit 
  (requires (fun h -> live h a /\ as_nat c h a < getPrime c)) 
  (ensures (fun h0 _ h1 -> modifies (loc a) h0 h1 /\ (
    let k = fromDomain_ #c (as_nat c h0 a) in 
    felem_eval c h1 a /\ as_nat c h1 a = toDomain_ #c (pow k (pow2 (v n))))))
