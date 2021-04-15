module Hacl.Impl.EC.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Mul


val montgomery_multiplication_reduction_dh: #c: curve
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ wide_as_nat c h t < getPrime c * pow2 (getPower c) /\ live h result /\ 
    eq_or_disjoint t result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result |+| loc t) h0 h1 /\ (let prime = getPrime c in 
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #DH (wide_as_nat c h0 t))))

val montgomery_multiplication_reduction_dsa: #c: curve
  -> t: widefelem c 
  -> result: felem c -> 
  Stack unit 
  (requires (fun h -> live h t /\ wide_as_nat c h t < getOrder #c * pow2 (getPower c) /\ live h result /\ 
    eq_or_disjoint t result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result |+| loc t) h0 h1 /\ (let prime = getOrder #c in 
    as_nat c h1 result = (wide_as_nat c h0 t * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #DSA (wide_as_nat c h0 t))))


val montgomery_multiplication_buffer_by_one_dh: #c: curve -> a: felem c -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ felem_eval c h a /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getPrime c in 
    as_nat c h1 result = (as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #DH (as_nat c h0 a))))

val montgomery_multiplication_buffer_by_one_dsa: #c: curve -> a: felem c -> result: felem c -> 
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getOrder #c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let prime = getOrder #c in 
    as_nat c h1 result = (as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = fromDomain_ #c #DSA (as_nat c h0 a))))


val montgomery_multiplication_buffer: #c: curve -> m: mode -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h result /\ eq_or_disjoint a b /\ 
    as_nat c h a < getModePrime m c /\ as_nat c h b < getModePrime m c)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime m c /\ (
    let prime = getModePrime m c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c #m (fromDomain_ #c #m (as_nat c h0 a) * fromDomain_ #c #m (as_nat c h0 b) % prime) /\
    as_nat c h1 result = toDomain_ #c #m (fromDomain_ #c #m (as_nat c h0 a) * fromDomain_ #c #m (as_nat c h0 b)))))

val montgomery_multiplication_buffer_dh: #c: curve -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h result /\ 
    eq_or_disjoint a b /\
    as_nat c h a < getModePrime DH c /\ as_nat c h b < getModePrime DH c))
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime DH c /\ (
    let prime = getModePrime DH c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime) % getPrime c /\
    as_nat c h1 result = toDomain_ #c #DH (fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 b) % prime) /\
    as_nat c h1 result = toDomain_ #c #DH (fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 b)))))

val montgomery_multiplication_buffer_dsa: #c: curve -> a: felem c -> b: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h result /\ as_nat c h a < getModePrime DSA c /\  eq_or_disjoint a b /\
    as_nat c h b < getModePrime DSA c))
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime DSA c /\ (
    let prime = getModePrime DSA c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 a) * fromDomain_ #c #DSA (as_nat c h0 b) % prime) /\
    as_nat c h1 result = toDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 a) * fromDomain_ #c #DSA (as_nat c h0 b)))))


val montgomery_square_buffer: #c: curve -> m: mode -> a: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime m c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime m c /\ (
    let prime = getModePrime m c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c #m (fromDomain_ #c #m (as_nat c h0 a) * fromDomain_ #c #m (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c #m (fromDomain_ #c #m (as_nat c h0 a) * fromDomain_ #c #m (as_nat c h0 a)))))

val montgomery_square_buffer_dh: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime DH c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime DH c /\ (
    let prime = getModePrime DH c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c #DH (fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c #DH (fromDomain_ #c #DH (as_nat c h0 a) * fromDomain_ #c #DH (as_nat c h0 a)))))

val montgomery_square_buffer_dsa: #c: curve -> a: felem c -> result: felem c ->  
  Stack unit
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime DSA c /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getModePrime DSA c /\ (
    let prime = getModePrime DSA c in 
    as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (pow2 (getPower c)) prime) % prime /\
    as_nat c h1 result = toDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 a) * fromDomain_ #c #DSA (as_nat c h0 a) % prime) /\
    as_nat c h1 result = toDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 a) * fromDomain_ #c #DSA (as_nat c h0 a)))))


val fsquarePowN_dh: #c: curve -> n: size_t -> a: felem c -> Stack unit 
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime DH c)) 
  (ensures (fun h0 _ h1 -> modifies (loc a) h0 h1 /\ (
    let k = fromDomain_ #c #DH (as_nat c h0 a) in 
    as_nat c h1 a < getModePrime DH c /\ as_nat c h1 a = toDomain_ #c #DH (pow k (pow2 (v n))))))

val fsquarePowN_dsa: #c: curve -> n: size_t -> a: felem c -> Stack unit 
  (requires (fun h -> live h a /\ as_nat c h a < getModePrime DSA c)) 
  (ensures (fun h0 _ h1 -> modifies (loc a) h0 h1 /\ (
    let k = fromDomain_ #c #DSA (as_nat c h0 a) in 
    as_nat c h1 a < getModePrime DSA c /\ as_nat c h1 a = toDomain_ #c #DSA (pow k (pow2 (v n))))))
