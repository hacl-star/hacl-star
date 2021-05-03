module Hacl.Impl.EC.Arithmetics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.EC.Lemmas
open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC

open Hacl.Spec.MontgomeryMultiplication

open FStar.Math.Lemmas
friend Hacl.Spec.MontgomeryMultiplication

open FStar.Mul

#set-options "--z3rlimit 200" 

let cube #c a result =
    let h0 = ST.get() in 
  montgomery_square_buffer_dh a result;
  montgomery_multiplication_buffer_dh result a result;
    let h1 = ST.get() in 
    lemma_mod_mul_distr_l (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)) (fromDomain #c (as_nat c h0 a)) (getPrime c);
    inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a))


let quatre #c a result = 
    let h0 = ST.get() in 
  montgomery_square_buffer_dh a result;
  montgomery_square_buffer_dh result result;

  let prime = getPrime c in 
  
  inDomain_mod_is_not_mod #c #DH ((fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) % prime) * (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) % prime));
    modulo_distributivity_mult2 (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)) (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)) 1 prime;
    lemma_multiplication_associative (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)) (fromDomain #c (as_nat c h0 a)) (fromDomain #c (as_nat c h0 a));
    inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a))


let multByTwo #c a out = 
  let h0 = ST.get() in 
  felem_add a a out;
  inDomain_mod_is_not_mod #c #DH (2 * fromDomain #c (as_nat c h0 a))


let multByThree #c a result = 
    let h0 = ST.get() in 
  multByTwo a result;
    let h1 = ST.get() in 
      assert(as_nat c h1 result == toDomain #c (2 * fromDomain #c (as_nat c h0 a) % getPrime c));
  felem_add a result result;
    let h2 = ST.get() in 
    lemma_mod_add_distr (fromDomain #c (as_nat c h0 a)) (2 * fromDomain #c (as_nat c h0 a)) (getPrime c);
    inDomain_mod_is_not_mod #c #DH (3 * fromDomain #c (as_nat c h0 a))
  

let multByFour #c a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result;

  let prime = getPrime c in 
    lemma_mod_mul_distr_r 2 (2 * fromDomain #c (as_nat c h0 a)) prime;
    lemma_multiplication_associative 2 2 (fromDomain #c (as_nat c h0 a)); 
    inDomain_mod_is_not_mod #c #DH (4 * fromDomain #c (as_nat c h0 a))


let multByEight #c a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result; 
  multByTwo result result; 

    let prime = getPrime c in 
    lemma_mod_mul_distr_r 2 (2 * fromDomain #c (as_nat c h0 a)) prime;
    lemma_multiplication_associative 2 2 (fromDomain #c (as_nat c h0 a)); 
    inDomain_mod_is_not_mod #c #DH (4 * fromDomain #c (as_nat c h0 a)); 
    lemma_mod_mul_distr_r 2 (4 * fromDomain #c (as_nat c h0 a)) prime;
    lemma_multiplication_associative 2 4 (fromDomain #c (as_nat c h0 a));
    inDomain_mod_is_not_mod #c #DH (8 * fromDomain #c (as_nat c h0 a))


let multByMinusThree #c a result  = 
  push_frame();
  
  multByThree a result;
  let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
  let zeros : felem c = create sz (u64 0) in
  let h0 = ST.get() in 
    lemma_create_zero_buffer (v (getCoordinateLenU64 c)) c;
  felem_sub zeros result result; 
  
  let prime = getPrime c in 
  lemmaFromDomain #c #DH 0; 

  assert(fromDomain #c 0 == 0 * modp_inv_prime (pow2 (getPower c)) prime % prime);
  assert_norm (0 * 0 * modp_inv_prime (pow2 (getPower c)) prime == 0);
  small_mod 0 prime;

  assert_norm (fromDomain #c 0 == 0); 

  lemma_mod_sub_distr 0 (3 * fromDomain #c (as_nat c h0 a)) prime;
  inDomain_mod_is_not_mod #c #DH ((-3) * fromDomain #c (as_nat c h0 a));
  pop_frame()

