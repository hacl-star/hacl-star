module Hacl.Impl.P256.LowLevel.PrimeSpecific

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication
open FStar.Mul


inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256} = 
  assert_norm (felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction
let prime384_buffer: x: glbuffer uint64 6ul {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list
p384_prime_list) /\ recallable x /\ felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384}  = 
  assert_norm (felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384);
  createL_global p384_prime_list


inline_for_extraction
let prime_buffer (#c: curve) (x: glbuffer uint64 (getCoordinateLenU64 c) {witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (prime_list c)) /\ recallable x /\ felem_seq_as_nat c (Lib.Sequence.of_list (prime_list c)) == getPrime c}) = 
  createL_global (prime_list c)


val reduction_prime_2prime_with_carry: #c: curve -> x: widefelem c -> result: felem c -> 
  Stack unit 
    (requires fun h -> 
      live h x /\ live h result /\ eq_or_disjoint x result /\ wide_as_nat c h x < 2 * getPrime c)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ as_nat c h1 result = wide_as_nat c h0 x % getPrime c)


val reduction_prime_2prime: #c: curve -> x: felem c -> result: felem c -> 
  Stack unit
    (requires fun h -> 
      live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\ as_nat c h1 result == as_nat c h0 x % getPrime c)


val felem_add: #c: curve -> a: felem c -> b: felem c -> out: felem c -> 
  Stack unit
    (requires (fun h0 -> 
      live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\  eq_or_disjoint b out /\
      as_nat c h0 a < getPrime c /\ as_nat c h0 b < getPrime c 
      )
    )
    (ensures (fun h0 _ h1 -> 
      modifies (loc out) h0 h1 /\ 
      as_nat c h1 out == (as_nat c h0 a + as_nat c h0 b) % getPrime c /\
      as_nat c h1 out == toDomain_ #c((fromDomain_ #c (as_nat c h0 a) + fromDomain_ #c (as_nat c h0 b)) % getPrime c)
	)
    )


val felem_double: #c: curve -> a: felem c -> out: felem c -> 
  Stack unit 
    (requires (fun h0 -> 
      live h0 a /\ live h0 out /\ eq_or_disjoint a out /\ as_nat c h0 a < getPrime c))
    (ensures (fun h0 _ h1 -> 
      modifies (loc out) h0 h1 /\ 
      as_nat c h1 out == (2 * as_nat c h0 a) % getPrime c /\
      as_nat c h1 out == toDomain_ #c (2 * fromDomain_ #c (as_nat c h0 a) % getPrime c)
    )
  )


val felem_sub: #c: curve -> a: felem c -> b: felem c -> out: felem c -> 
  Stack unit 
    (requires (fun h0 -> 
      live h0 out /\ live h0 a /\ live h0 b /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ 
      as_nat c h0 a < getPrime c /\ as_nat c h0 b < getPrime c
      )
    )
    (ensures (fun h0 _ h1 -> 
      modifies (loc out) h0 h1 /\ 
      as_nat c h1 out == (as_nat c h0 a - as_nat c h0 b) % getPrime c /\
      as_nat c h1 out == toDomain_ #c ((fromDomain_ #c (as_nat c h0 a) - fromDomain_ #c (as_nat c h0 b)) % getPrime c)
      )
    )    
