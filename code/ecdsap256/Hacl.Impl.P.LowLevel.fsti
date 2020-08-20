module Hacl.Impl.P.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Spec.P256
open FStar.Mul
open Hacl.Spec.P256.MontgomeryMultiplication


#set-options "--z3rlimit 100"


inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256} = 
  assert_norm (felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction
let prime384_buffer: x: glbuffer uint64 6ul {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list
p384_prime_list) /\ recallable x /\ felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384}  = 
  assert_norm (felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384);
  createL_global p384_prime_list


val uploadZeroImpl: #c: curve -> f: felem c -> Stack unit 
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> as_nat c h1 f == 0 /\ modifies (loc f) h0 h1)


val uploadZeroPoint: #c: curve -> p: point c -> 
  Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 ->
    let len = getCoordinateLenU64 c in 
    modifies (loc p) h0 h1 /\
    as_nat c h1 (gsub p (size 0) len) == 0 /\ 
    as_nat c h1 (gsub p len len) == 0 /\
    as_nat c h1 (gsub p (size 2 *! len) len) == 0) 


val cmovznz4: #c: curve -> cin: uint64 -> x: felem c -> y: felem c -> result: felem c ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ 
      eq_or_disjoint y result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ (
      if uint_v cin = 0 then 
	as_nat c h1 result == as_nat c h0 x 
      else 
	as_nat c h1 result == as_nat c h0 y))


val add_bn: #c: curve -> x: felem c -> y: felem c -> result: felem c -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ v r <= 1 /\ 
      as_nat c h1 result + v r * getPower2 c == as_nat c h0 x + as_nat c h0 y)   


val add_long_bn: #c: curve -> x: widefelem c -> y: widefelem c -> result: widefelem c -> 
  Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ v r <= 1 /\ 
    wide_as_nat c h1 result + v r * getLongPower2 c == wide_as_nat c h0 x + wide_as_nat c h0 y)


val add_dep_prime: #c: curve -> x: felem c -> t: uint64 {uint_v t == 0 \/ uint_v t == 1} -> result: felem c -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
      if uint_v t = 1 then 
	as_nat c h1 result + uint_v r * getPower2 c == as_nat c h0 x + getPrime c
      else
	as_nat c h1 result  == as_nat c h0 x))  
 

val sub_bn: #c: curve -> x: felem c -> y:felem c -> result: felem c -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 r h1 -> modifies1 result h0 h1 /\ v r <= 1 /\ 
      as_nat c h1 result - v r * getPower2 c == as_nat c h0 x - as_nat c h0 y)


val sub_bn_gl: #c: curve -> x: felem c -> y: glbuffer uint64 (getCoordinateLenU64 c) -> 
  result: felem c -> Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ disjoint y result)
    (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ v r <= 1 /\ 
      as_nat c h1 result - v r * getPower2 c == as_nat c h0 x  - as_nat_il c h0 y /\ (
      if uint_v r = 0 then 
	as_nat c h0 x >= as_nat_il c h0 y 
      else 
	as_nat c h0 x < as_nat_il c h0 y))


val short_mul_bn: #c: curve -> a: glbuffer uint64 (getCoordinateLenU64 c) -> b: uint64 -> result: widefelem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ wide_as_nat c h result = 0)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat_il c h0 a * uint_v b = wide_as_nat c h1 result /\ 
    wide_as_nat c h1 result < getPower2 c * pow2 64)


val square_bn: #c: curve -> f: felem c -> out: widefelem c -> Stack unit
    (requires fun h -> live h out /\ live h f /\ eq_or_disjoint f out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat c h1 out = as_nat c h0 f * as_nat c h0 f)
      

val uploadOneImpl: #c: curve -> f: felem c -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> as_nat c h1 f == 1 /\ modifies (loc f) h0 h1)


val toUint8: #c: curve -> i: felem c ->  o: lbuffer uint8 (getScalarLen c) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
      as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be (as_seq h0 i))


val changeEndian: #c: curve -> i: felem c -> Stack unit 
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 (*/\ 
    as_seq h1 i == Hacl.Spec.ECDSA.Definition.changeEndian (as_seq h0 i) /\
    as_nat P256 h1 i < pow2 256 *) ) 

val toUint64ChangeEndian: #c: curve -> i:lbuffer uint8 (getScalarLen c) -> o: felem c -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 ->
    modifies (loc o) h0 h1 (* /\
    as_seq h1 o == Hacl.Spec.ECDSA.Definition.changeEndian (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)) *)
  )



inline_for_extraction
let prime_buffer (#c: curve): (x: glbuffer uint64 (getCoordinateLenU64 c) {witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (prime_list c)) /\ recallable x /\ felem_seq_as_nat c (Lib.Sequence.of_list (prime_list c)) == getPrime c}) = 
  match c with
  | P256 -> prime256_buffer
  | P384 -> prime384_buffer


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



inline_for_extraction noextract
val mul: #c: curve -> f: felem c -> r: felem c -> out: widefelem c -> 
  Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r /\ disjoint r out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat c h1 out = as_nat c h0 r * as_nat c h0 f
    )



  
val eq0_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0})

val eq1_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == 0 else uint_v r == pow2 64 - 1})


val isZero_uint64_CT: #c: curve ->  f: felem c -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    (if as_nat c h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))
 


 val compare_felem: #c: curve -> a: felem c -> b: felem c -> Stack uint64
  (requires fun h -> live h a /\ live h b) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if as_nat c h0 a = as_nat c h0 b then uint_v r == pow2 64 - 1 else uint_v r = 0))


val copy_conditional: #c: curve -> out: felem c -> x: felem c 
  -> mask: uint64 {uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    (if uint_v mask = 0 then as_seq h1 out == as_seq h0 out else as_seq h1 out == as_seq h0 x)) 


val shiftLeftWord: #c: curve -> i: felem c -> o: lbuffer uint64 (getCoordinateLenU64 c *. 2ul)-> 
  Stack unit 
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ wide_as_nat c h1 o == as_nat c h0 i * getPower2 c)


inline_for_extraction noextract
val mod64: #c: curve -> a: widefelem c -> Stack uint64 
  (requires fun h -> live h a) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ wide_as_nat c h1 a % pow2 64 = uint_v r)



val shift1: #c: curve -> t: widefelem c -> t1: widefelem c -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ eq_or_disjoint t t1)
  (ensures fun h0 _ h1 -> modifies (loc t1) h0 h1 /\ 
    wide_as_nat c h0 t / pow2 64 = wide_as_nat c h1 t1)



inline_for_extraction noextract 
val upload_one_montg_form: #c: curve -> b: felem c -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 )



inline_for_extraction noextract
val scalar_bit:
    #c: curve -> 
    #buf_type: buftype -> 
    s:lbuffer_t buf_type uint8 (getScalarLen c)
  -> n:size_t{v n < getScalarLenNat c}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)
      
