module Hacl.Impl.ECDSA.MM.Exponent


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.EC.Math 

open Hacl.Impl.EC.LowLevel 
open Hacl.EC.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon 

open Hacl.Impl.EC.MontgomeryMultiplication
open FStar.Mul

open Lib.Loops
open Hacl.Spec.EC.Definition

open Hacl.Spec.ECDSA.Definition
open Hacl.Impl.MM.Exponent

#reset-options " --z3rlimit 200"


let montgomery_ladder_exponent #c r = 
  push_frame(); 
    let p = create (size 4) (u64 0) in  
    upload_one_montg_form #c p; 
    recall_contents (order_inverse_buffer #P256) (prime_order_inverse_seq #P256);
    let h = ST.get() in
    mut_const_immut_disjoint #uint64 #uint8 p (order_inverse_buffer #P256) h;
    mut_const_immut_disjoint #uint64 #uint8 r (order_inverse_buffer #P256) h;
    assert (disjoint p (order_inverse_buffer #P256));
    assert (disjoint r (order_inverse_buffer #P256));
    _montgomery_ladder_power #c #DSA p r (order_inverse_buffer #P256);
      lemmaToDomainFromDomain #c #DSA 1;
    copy r p;
  pop_frame()  


let fromDomainImpl #c a result = 
  push_frame();
    let one = create (size 4) (u64 0) in 
    uploadOneImpl #c one;
    montgomery_multiplication_buffer_dsa one a result;
  pop_frame()   


val lemma_fromDomain1: #c: curve -> a: nat -> 
  Lemma ((fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA a))) == ((a * modp_inv2_prime (pow2 256) prime_p256_order * modp_inv2_prime (pow2 256) prime_p256_order * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order))

let lemma_fromDomain1 a = 
  let f = modp_inv2_prime (pow2 256) prime_p256_order in 
  lemma_mod_mul_distr_l (a * f) f prime_p256_order; 
  lemma_mod_mul_distr_l (a * f * f) f prime_p256_order


val lemma_fromDomain2: #c: curve -> a: nat -> 
  Lemma (pow (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) (prime_p256_order - 2) % prime_p256_order == 
    (
      pow a (prime_p256_order - 2) * 
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) * 
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2)) % prime_p256_order /\
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) * pow (pow2 256) (prime_p256_order -2) % prime_p256_order == 1
    )


let lemma_fromDomain2 a = 
  let r = modp_inv2_prime (pow2 256) prime_p256_order in 
  lemma_mod_mul_distr_l (a * r) r prime_p256_order;
  power_distributivity (a * r * r) (prime_p256_order - 2) prime_p256_order;
    assert_by_tactic (a * r * r == a * (r * r)) canon;
  power_distributivity_2 a (r * r) (prime_p256_order - 2);
  power_distributivity_2 (modp_inv2_prime (pow2 256) prime_p256_order) (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order -2);
  assert_by_tactic (pow a (prime_p256_order - 2) * (
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) * 
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2)) == 
      pow a (prime_p256_order - 2) * 
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) * 
      pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2)) canon;

  let inv_pow256_order = 43790243014242295660885426880012836369732278457577312309071968676491870960761 in 
  assert_norm (modp_inv2_prime (pow2 256) prime_p256_order == inv_pow256_order);
  assert_norm (inv_pow256_order * (pow2 256) % prime_p256_order == 1);
  power_distributivity_2 (inv_pow256_order) (pow2 256) (prime_p256_order - 2);
  power_distributivity (inv_pow256_order * pow2 256) (prime_p256_order - 2) prime_p256_order;
  power_one (prime_p256_order -2)


let multPower #c a b result = 
  push_frame();
    let tempB1 = create (size 4) (u64 0) in 
    let buffFromDB = create (size 4) (u64 0) in 
	let h0 = ST.get() in 
      fromDomainImpl #c a tempB1;
      fromDomainImpl #c b buffFromDB;
      fromDomainImpl #c buffFromDB buffFromDB;
      montgomery_ladder_exponent #c tempB1;
      montgomery_multiplication_buffer_dsa tempB1 buffFromDB result;
    pop_frame();
    
      let p = pow (fromDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 a))) (prime_p256_order - 2) % prime_p256_order in 
      let q = fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 b))) in 
      let r = modp_inv2_prime (pow2 256) prime_p256_order in 
      lemma_fromDomain1 #c (as_nat c h0 b);
      lemma_fromDomain2 #c (as_nat c h0 a);

      lemma_mod_mul_distr_l (pow (as_nat c h0 a) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2)) (((as_nat c h0 b) * r * r * r) % prime_p256_order) prime_p256_order;
      lemma_mod_mul_distr_r (pow (as_nat c h0 a) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2)) ((as_nat c h0 b) * r * r * r) prime_p256_order;

      assert_by_tactic (pow (as_nat c h0 a) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2) * ((as_nat c h0 b) * r * r * r) == pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 2) * r) * (pow r (prime_p256_order - 2) * r) * (as_nat c h0 b) * r) canon;

      pow_plus r (prime_p256_order - 2) 1; 
      power_one r; 
      lemma_mod_mul_distr_l (pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * r) (pow2 256) prime_p256_order;
      
      assert_by_tactic (pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * r * pow2 256 == pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * (r * pow2 256)) canon;
      lemma_mod_mul_distr_r (pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b)) (r * pow2 256) prime_p256_order;

      assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order == 1);
      assert_by_tactic (pow (as_nat c h0 a) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) == pow (as_nat c h0 a) (prime_p256_order - 2) * (as_nat c h0 b)  * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1))) canon;

      lemma_mod_mul_distr_r (pow (as_nat c h0 a) (prime_p256_order - 2) * (as_nat c h0 b)  * (pow r (prime_p256_order - 1))) (pow r (prime_p256_order - 1)) prime_p256_order;

      lemma_l_ferm ();
      lemma_mod_mul_distr_r (pow (as_nat c h0 a) (prime_p256_order - 2) * (as_nat c h0 b)) (pow r (prime_p256_order - 1)) prime_p256_order


let multPowerPartial #c s a b result = 
  let h0 = ST.get() in 
  push_frame();
    let buffFromDB = create (size 4) (u64 0) in 
    fromDomainImpl #c b buffFromDB;
    fromDomainImpl #c buffFromDB buffFromDB;
    montgomery_multiplication_buffer_dsa a buffFromDB result;
  pop_frame();

    let p = pow (fromDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 s))) (prime_p256_order - 2) % prime_p256_order in 
    let q = fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA (as_nat c h0 b))) in 
    let r = modp_inv2_prime (pow2 256) prime_p256_order in 
      lemma_fromDomain1 #c (as_nat c h0 b);
      lemma_fromDomain2 #c (as_nat c h0 s);

      lemma_mod_mul_distr_l (pow (as_nat c h0 s) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2)) (((as_nat c h0 b) * r * r * r) % prime_p256_order) prime_p256_order;
      lemma_mod_mul_distr_r (pow (as_nat c h0 s) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2)) ((as_nat c h0 b) * r * r * r) prime_p256_order;
      assert_by_tactic (pow (as_nat c h0 s) (prime_p256_order - 2) * pow r (prime_p256_order - 2) * pow r (prime_p256_order - 2) * ((as_nat c h0 b) * r * r * r) == pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 2) * r) * (pow r (prime_p256_order - 2) * r) * (as_nat c h0 b) * r) canon;
    
      pow_plus r (prime_p256_order - 2) 1; 
      power_one r;
      lemma_mod_mul_distr_l (pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * r) (pow2 256) prime_p256_order;
      
      assert_by_tactic (pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * r * pow2 256 == pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) * (r * pow2 256)) canon;
      lemma_mod_mul_distr_r (pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b)) (r * pow2 256) prime_p256_order;
      assert_norm ((pow2 256 * modp_inv2_prime (pow2 256) prime_p256_order) % prime_p256_order == 1);
      
      assert_by_tactic (pow (as_nat c h0 s) (prime_p256_order - 2) * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1)) * (as_nat c h0 b) == pow (as_nat c h0 s) (prime_p256_order - 2) * (as_nat c h0 b)  * (pow r (prime_p256_order - 1)) * (pow r (prime_p256_order - 1))) canon;
      lemma_mod_mul_distr_r (pow (as_nat c h0 s) (prime_p256_order - 2) * (as_nat c h0 b)  * (pow r (prime_p256_order - 1))) (pow r (prime_p256_order - 1)) prime_p256_order;
      lemma_l_ferm ();
      
      lemma_mod_mul_distr_r (pow (as_nat c h0 s) (prime_p256_order - 2) * (as_nat c h0 b)) (pow r (prime_p256_order - 1)) prime_p256_order

