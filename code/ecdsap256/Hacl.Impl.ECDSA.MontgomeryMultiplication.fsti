module Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Spec.P256
open Hacl.Spec.ECDSA.Definition
open Spec.ECDSA
open Hacl.Impl.P256.LowLevel 
  

open FStar.Mul

noextract
let prime = prime_p256_order

inline_for_extraction
let prime256order_buffer: x: glbuffer uint64 (size 4)  
  {witnessed #uint64 #(size 4) x 
  (Lib.Sequence.of_list p256_order_prime_list) /\ recallable x /\ 
  felem_seq_as_nat (Lib.Sequence.of_list (p256_order_prime_list)) == prime_p256_order} = 
  createL_global p256_order_prime_list


inline_for_extraction
let order_inverse_buffer: x: glbuffer uint8 32ul {witnessed x (prime_order_inverse_seq #P256) /\ recallable x} = 
  createL_global (prime_order_inverse_list #P256)


inline_for_extraction
let order_buffer: x: glbuffer uint8 32ul {witnessed x (prime_order_seq #P256) /\ recallable x} = 
  createL_global (prime_order_list #P256)


val reduction_prime_2prime_with_carry: #c: curve -> x: widefelem c -> result: felem c ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ wide_as_nat c h x < 2 * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = wide_as_nat c h0 x % prime_p256_order)  
    
inline_for_extraction noextract
val reduction_prime_2prime_with_carry2: #c: curve ->  carry: uint64 ->  x: felem c 
  -> result: felem c ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ 
      uint_v carry * pow2 256 + as_nat c h x < 2 * prime_p256_order )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
      as_nat c h1 result = (uint_v carry * pow2 256 + as_nat c h0 x) % prime_p256_order)  


val reduction_prime_2prime_order: #c: curve -> x: felem c 
  -> result: felem c -> 
  Stack unit 
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  as_nat c h1 result == as_nat c h0 x % prime_p256_order)  


noextract
val fromDomain_: a: nat -> Tot (r: nat { r < prime})

noextract
val toDomain_: a: nat -> Tot nat

val lemmaFromDomain: a: nat ->  Lemma (
  (a * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order == fromDomain_ a)

val lemmaToDomain: a: nat ->  Lemma (
  (a * pow2 256) % prime_p256_order == toDomain_ a)


val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaToDomainFromDomain: a: nat { a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)


val montgomery_multiplication_ecdsa_module: #c: curve -> a: felem c -> b: felem c 
  ->result: felem c -> 
  Stack unit 
    (requires fun h -> live h a /\ live h b /\ live h result /\
      as_nat c h a < prime_p256_order /\ as_nat c h b < prime_p256_order)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ 
      as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order /\ 
      as_nat c h1 result = toDomain_ (fromDomain_ (as_nat c h0 a) * fromDomain_ (as_nat c h0 b) % prime_p256_order))


inline_for_extraction noextract
val felem_add: #c: curve -> arg1: felem c -> arg2: felem c -> out: felem c -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat c h0 arg1 < prime_p256_order /\ as_nat c h0 arg2 < prime_p256_order
   )
  )
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat c h1 out == (as_nat c h0 arg1 + as_nat c h0 arg2) % prime_p256_order))

val lemma_felem_add: a: nat -> b: nat -> Lemma ((fromDomain_ a + fromDomain_ b) % prime_p256_order = fromDomain_ (a + b))
