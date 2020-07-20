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
 lemma_mod_mul_distr_l (fromDomain_ (as_nat c h0 a) * fromDomain_ (as_nat c h0 a)) (fromDomain_ (as_nat c h0 a)) (getPrime c);
inDomain_mod_is_not_mod (fromDomain_ (as_nat c h0 a) * fromDomain_ (as_nat c h0 a) * fromDomain_ (as_nat c h0 a)); 
  admit()


let quatre a result = 
    let h0 = ST.get() in 
  montgomery_square_buffer a result;
  montgomery_square_buffer result result ;
    admit()
    (*inDomain_mod_is_not_mod ((fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) * (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256));
    modulo_distributivity_mult2 (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)) 1 prime256;
    lemma_brackets (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 a));
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)) *)


let multByTwo a out = 
  let h0 = ST.get() in 
  felem_add a a out (*;
    inDomain_mod_is_not_mod (2 * fromDomain_ (as_nat h0 a)) *)


let multByThree a result = 
    let h0 = ST.get() in 
  multByTwo a result;
    let h1 = ST.get() in (*
      assert(as_nat h1 result == toDomain_ (2 * fromDomain_ (as_nat h0 a) % prime256)); *)
  felem_add a result result;
  admit() 
  (*;
    let h2 = ST.get() in 
    lemma_mod_add_distr (fromDomain_ (as_nat h0 a)) (2 * fromDomain_ (as_nat h0 a)) prime256;
    inDomain_mod_is_not_mod (3 * fromDomain_ (as_nat h0 a)) *)
  

let multByFour a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result;
   admit () (*
    lemma_mod_mul_distr_r 2 (2 * fromDomain_ (as_nat h0 a)) prime256;
    lemma_brackets 2 2 (fromDomain_ (as_nat h0 a)); 
    inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat h0 a)) *)


let multByEight a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result; (*
    lemma_mod_mul_distr_r 2 (2 * fromDomain_ (as_nat h0 a)) prime256;
    lemma_brackets 2 2 (fromDomain_ (as_nat h0 a)); 
    inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat h0 a)); *)
  multByTwo result result; 
  admit() (*
    lemma_mod_mul_distr_r 2 (4 * fromDomain_ (as_nat h0 a)) prime256;
    lemma_brackets 2 4 (fromDomain_ (as_nat h0 a));
    inDomain_mod_is_not_mod (8 * fromDomain_ (as_nat h0 a))
*)


let multByMinusThree #c a result  = 
  let h0 = ST.get() in 
    push_frame();
    multByThree a result;
    let zeros = create (size (getCoordinateLenU64 c)) (u64 0) in 
    felem_sub zeros result result; 
    admit();
    
    (*
      lemmaFromDomain 0; 
      assert_norm( 0 * modp_inv2 #P256 (pow2 256) % prime256 == 0);
      assert_norm (fromDomain_ 0 == 0); 
      lemma_mod_sub_distr 0 (3 * fromDomain_ (as_nat h0 a)) prime256;
      inDomain_mod_is_not_mod ((-3) * fromDomain_ (as_nat h0 a));   *)
  pop_frame()

