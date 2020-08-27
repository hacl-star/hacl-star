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

#set-options "--z3rlimit 200"


val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c /\
    eq_or_disjoint t round)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (wide_as_nat c h0 t % pow2 64)) / pow2 64)


val montgomery_multiplication_round_: #c: curve -> t: widefelem c -> t2: widefelem c -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  

let montgomery_multiplication_round_ #c t t2 =
  let t1 = mod64 t in 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
  short_mul_bn (prime_buffer #c) t1 t2
  


let montgomery_multiplication_round #c t round =
  push_frame(); 
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    
    let t2 = create (size 2 *! len) (u64 0) in 
    montgomery_multiplication_round_ #c t t2;
      admit();
    add_long_without_carry t t2 round;
    shift1 round round; 
    admit();
  pop_frame()  



val montgomery_multiplication_round_k0: #c: curve -> t: widefelem c 
  ->  round: widefelem c -> k0: uint64 ->
  Stack unit 
    (requires fun h -> live h t /\ live h round  /\ wide_as_nat c h t < prime_p256_order * prime_p256_order)
    (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\ 
      wide_as_nat c h1 round = (wide_as_nat c h0 t + prime_p256_order * ((uint_v k0 * (wide_as_nat c h0 t % pow2 64)) % pow2 64)) / pow2 64)

let montgomery_multiplication_round_k0 #c t round k0 = 
  push_frame(); 
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    
    let temp = create (size 1) (u64 0) in 
    let y = create (size 1) (u64 0) in 

    let t2 = create (size 2 *! len) (u64 0) in 
    let t3 = create (size 2 *! len) (u64 0) in 
    let t1 = mod64 #c t in
    
    mul_atomic t1 k0 y temp;
    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
    let y_ = index y (size 0) in   
    short_mul_bn #c (prime_buffer #c) y_ t2;
    add_long_without_carry #c t t2 t3;
    shift1 #c t3 round;
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
    
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
    mul_lemma_ (as_nat P256 h0 a) (as_nat P256 h0 a) prime256;

  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result; 
   
  pop_frame()  

