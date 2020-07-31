module Hacl.Impl.P256.Arithmetics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Lemmas.P256
open Hacl.Spec.P256.Definition

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256

open Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
friend Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Mul

#set-options "--z3rlimit 200" 

let cube #c a result =
  let h0 = ST.get() in 
    montgomery_square_buffer a result;
    montgomery_multiplication_buffer result a result;
 let h1 = ST.get() in 
 lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 a)) (getPrime c);
inDomain_mod_is_not_mod #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a))


let quatre #c a result = 
    let h0 = ST.get() in 
  montgomery_square_buffer a result;
  montgomery_square_buffer result result;

  let prime = getPrime c in 
  
  inDomain_mod_is_not_mod #c ((fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) * (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime));
    modulo_distributivity_mult2 (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)) 1 prime;
    lemma_brackets (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 a));
    inDomain_mod_is_not_mod #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a))


let multByTwo #c a out = 
  let h0 = ST.get() in 
  felem_add a a out;
  inDomain_mod_is_not_mod #c (2 * fromDomain_ #c (as_nat c h0 a))


let multByThree #c a result = 
    let h0 = ST.get() in 
  multByTwo a result;
    let h1 = ST.get() in 
      assert(as_nat c h1 result == toDomain_ #c (2 * fromDomain_ #c (as_nat c h0 a) % getPrime c));
  felem_add a result result;
    let h2 = ST.get() in 
    lemma_mod_add_distr (fromDomain_ #c (as_nat c h0 a)) (2 * fromDomain_ #c (as_nat c h0 a)) (getPrime c);
    inDomain_mod_is_not_mod #c (3 * fromDomain_ #c (as_nat c h0 a))
  

let multByFour #c a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result;

  let prime = getPrime c in 
    lemma_mod_mul_distr_r 2 (2 * fromDomain_ #c (as_nat c h0 a)) prime;
    lemma_brackets 2 2 (fromDomain_ #c (as_nat c h0 a)); 
    inDomain_mod_is_not_mod #c (4 * fromDomain_ #c (as_nat c h0 a))


let multByEight #c a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result; 
  multByTwo result result; 

    let prime = getPrime c in 
    lemma_mod_mul_distr_r 2 (2 * fromDomain_ #c (as_nat c h0 a)) prime;
    lemma_brackets 2 2 (fromDomain_ #c (as_nat c h0 a)); 
    inDomain_mod_is_not_mod #c (4 * fromDomain_ #c (as_nat c h0 a)); 
    lemma_mod_mul_distr_r 2 (4 * fromDomain_ #c (as_nat c h0 a)) prime;
    lemma_brackets 2 4 (fromDomain_ #c (as_nat c h0 a));
    inDomain_mod_is_not_mod #c (8 * fromDomain_ #c (as_nat c h0 a))


let multByMinusThree #c a result  = 
  let h0 = ST.get() in 
    push_frame();
    multByThree a result;
    
    let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
    let zeros = create sz (u64 0) in 
    felem_sub zeros result result; 


      let prime = getPrime c in 
      lemmaFromDomain #c 0; 

      assert_norm(0 * modp_inv2 #P256 (getPower2 P256) % getPrime P256 == 0);
      assert_norm(0 * modp_inv2 #P384 (getPower2 P384) % getPrime P384 == 0);

      assert_norm(0 * modp_inv2 #c (getPower2 c) % getPrime c == 0);

      assert_norm (fromDomain_ #c 0 == 0); 

      lemma_mod_sub_distr 0 (3 * fromDomain_ #c (as_nat c h0 a)) prime;
      inDomain_mod_is_not_mod #c ((-3) * fromDomain_ #c (as_nat c h0 a));  
  pop_frame()

