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


#set-options " --z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let montgomery_ladder_exponent #c a r = 
  recall_contents (order_inverse_buffer #c) (prime_order_inverse_seq #c);
  montgomery_ladder_power #c #DSA a (order_inverse_buffer #c) r

let fromDomainImpl #c a result = 
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let one = create len (u64 0) in 
    uploadOneImpl #c one;
    montgomery_multiplication_buffer_dsa one a result;
    lemmaFromDomain #c #DSA (as_nat c h0 a);
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
    let len = getCoordinateLenU64 c in 
    let tempB1 = create len (u64 0) in 
    let buffFromDB = create len (u64 0) in 
	let h0 = ST.get() in 
      fromDomainImpl #c a tempB1;
      fromDomainImpl #c b buffFromDB;
	let h1 = ST.get() in 
      fromDomainImpl #c buffFromDB buffFromDB;
	let h2 = ST.get() in 
      montgomery_ladder_exponent #c tempB1 tempB1;
      montgomery_multiplication_buffer_dsa tempB1 buffFromDB result;
      	let h3 = ST.get() in 
    pop_frame();
 
  let a = as_nat c h0 a in 
  let b = as_nat c h0 b in 
  let order = getOrder #c in 
  let r = modp_inv2_prime (pow2 (getPower c)) order in  

  lemma_exp_not_zero order (pow2 (getPower c) % order) (order - 2);
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero order (r % order) (r % order);
  lemma_mod_mul_distr_l r (r % order) order;
  lemma_mod_mul_distr_r r r order;

  calc (==) {
    pow (r * r) (order - 2) * r * r % order;
    (==) {assert_by_tactic (pow (r * r) (order - 2) * r * r == (r * r) * pow (r * r) (order - 2)) canon} 
    (r * r) * pow (r * r) (order - 2) % order; 
    (==) {lemma_mod_mul_distr_r (r * r) (pow (r * r) (order - 2)) order}
    (r * r) * (pow (r * r) (order - 2) % order) % order;  
    (==) {power_distributivity (r * r) (order - 2) order}
    (r * r) * (pow (r * r % order) (order - 2) % order) % order; 
    (==) {lemma_pow_mod_n_is_fpow order (r * r % order) (order - 2)}
    (r * r) * (Spec.ECC.Curves.modp_inv2_prime (r * r) order) % order; 
    (==) {Hacl.Spec.MontgomeryMultiplication.lemma_mod_inv2_mult_prime order (r * r)}
    1;};


  calc (==) {
    toDomain_ #c #DSA (exponent_spec #c (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order);
    (==) {} 
    toDomain_ #c #DSA (pow (fromDomain_ #c #DSA (fromDomain_ #c #DSA a)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA a}
    toDomain_ #c #DSA (pow (fromDomain_ #c #DSA (a * r % order)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA (a * r % order)}
    toDomain_ #c #DSA (pow ((a * r % order * r % order)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemma_mod_mul_distr_l (a * r) r order}
    toDomain_ #c #DSA (pow (a * r * r % order) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {power_distributivity (a * r * r) (order - 2) order}
    toDomain_ #c #DSA (pow (a * r * r) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {assert_by_tactic (a * r * r == a * (r * r)) canon}
    toDomain_ #c #DSA (pow (a * (r * r)) (order - 2) % order * fromDomain_ #c #DSA (fromDomain_ #c #DSA (fromDomain_ #c #DSA b)) % order); 
    (==) {lemmaFromDomain #c #DSA b; lemmaFromDomain #c #DSA (b * r % order)}
    toDomain_ #c #DSA (pow (a * (r * r)) (order - 2) % order * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {power_distributivity_2 a (r * r) (order - 2)}
    toDomain_ #c #DSA ((pow a (order - 2) * pow (r * r) (order - 2)) % order * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (pow a (order - 2) * pow (r * r) (order - 2)) (fromDomain_ #c #DSA ((b * r % order) * r % order)) order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * fromDomain_ #c #DSA ((b * r % order) * r % order) % order); 
    (==) {lemmaFromDomain #c #DSA ((b * r % order) * r % order)}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * ((b * r % order) * r % order * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (b * r) r order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r % order * r % order) % order); 
    (==) {lemma_mod_mul_distr_l (b * r * r) r order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r % order) % order); 
    (==) {lemma_mod_mul_distr_r (pow a (order - 2) * pow (r * r) (order - 2)) (b * r * r * r) order}
    toDomain_ #c #DSA (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r) % order); 
    (==) {assert_by_tactic (pow a (order - 2) * pow (r * r) (order - 2) * (b * r * r * r) == 
      (r * (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)))) canon}
    toDomain_ #c #DSA (r * (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)) % order); 
    (==) {lemmaFromDomain #c #DSA ((pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)))}
    toDomain_ #c #DSA (fromDomain_ #c #DSA (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r))); 
    (==) {lemmaToDomainFromDomainModuloPrime #c #DSA (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r))}
    (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r)) % order; 
    (==) {lemma_mod_mul_distr_r (pow a (order - 2) * b) (pow (r * r) (order - 2) * r * r) order}
    (pow a (order - 2) * b * (pow (r * r) (order - 2) * r * r % order)) % order;}



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

