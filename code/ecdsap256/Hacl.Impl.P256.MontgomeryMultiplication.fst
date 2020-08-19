module Hacl.Impl.P256.MontgomeryMultiplication

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

open Hacl.Impl.P.LowLevel

open Lib.Loops
open Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100"


inline_for_extraction noextract
val add_long_without_carry: #c: curve -> t: widefelem c -> t1: widefelem c -> result: widefelem c -> Stack unit
  (requires fun h -> 
    live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ 
    wide_as_nat c h t1 < getPower2 c * pow2 64 /\ 
    wide_as_nat c h t < getPrime c * getPrime c
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    wide_as_nat c h1 result = wide_as_nat c h0 t + wide_as_nat c h0 t1)


let add_long_without_carry #c t t1 result  = 
  let _  = add_long_bn t t1 result in 
    assert_norm (getPower2 P256 * pow2 64 + getPrime P256 * getPrime P256 < getLongPower2 P256);
    assert_norm (getPower2 P384 * pow2 64 + getPrime P384 * getPrime P384 < getLongPower2 P384)


val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (wide_as_nat c h0 t % pow2 64)) / pow2 64
  )


let montgomery_multiplication_round #c t round =
  push_frame(); 
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    
    let t2 = create (size 2 *! len) (u64 0) in 
    let t3 = create (size 2 *! len) (u64 0) in 
    let t1 = mod64 t in 
    
      recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
    short_mul_bn (prime_buffer #c) t1 t2; 
    add_long_without_carry t t2 t3;
    shift1 t3 round; 
    admit();
  pop_frame()  


val montgomery_multiplication_one_round_proof: 
  #c: curve ->
  t: nat {t <  getPrime c * getPrime c} -> 
  result: nat {result = (t + (t % pow2 64) * getPrime c) / pow2 64} ->
  co: nat {co % getPrime c == t % getPrime c} -> 
  Lemma (
    result % getPrime c == co * modp_inv2 #c (pow2 64) % getPrime c /\
    result < getPrime c * getPrime c)


let montgomery_multiplication_one_round_proof t result co = 
  admit();
  mult_one_round t co;
  mul_lemma_1 (t % pow2 64) (pow2 64) prime256;
  assert_norm (prime256 * prime256 + pow2 64 * prime256 < pow2 575);
  lemma_div_lt (t + (t % pow2 64) * prime256) 575 64; 
  assert_norm (prime256 * prime256 > pow2 (575 - 64))


let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 
  copy t_low a; 

  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result;
  pop_frame()  



let montgomery_multiplication_buffer #c a b result = 
  assert_norm(prime256 > 3);
  push_frame();
  let len = getCoordinateLenU64 c in 
  
  let round = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  mul a b round;  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    True in 

  for 0ul len inv (fun i -> montgomery_multiplication_round #c round round);
      
  reduction_prime_2prime_with_carry round result; 
  pop_frame()  


let montgomery_square_buffer #c a result = 
  assert_norm(prime256 > 3);
  push_frame();
    
  let t = create (size 8) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
    mul_lemma_ (as_nat P256 h0 a) (as_nat P256 h0 a) prime256;

  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result; 
   
  pop_frame()  

