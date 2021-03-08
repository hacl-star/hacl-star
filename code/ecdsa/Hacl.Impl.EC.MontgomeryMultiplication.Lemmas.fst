module Hacl.Impl.EC.MontgomeryMultiplication.Lemmas


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

open Hacl.Impl.EC.LowLevel

open Lib.Loops
open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.EC.Setup


#set-options "--z3rlimit 200"



val lemma_add_lt: a : int -> b: int -> q: int -> q1: int -> Lemma
  (requires (a < q /\ b < q1))
  (ensures (a + b < q + q1))

let lemma_add_lt a b q q1 = ()

val lemma_one_round_0: a: nat -> b1: nat -> b2: nat -> Lemma 
  (requires (a <= (b1 + pow2 64 * b2) / pow2 64))
  (ensures (a <= b1 / pow2 64 + b2))

let lemma_one_round_0 a b1 b2 =
  lemma_div_plus b1 b2 (pow2 64)



val montgomery_multiplication_one_round_proof_border: #c: curve ->
  z: nat {z < pow2 64} -> 
  t: nat {t < getPrime c * getPrime c} -> 
  result: nat {result = (t + getPrime c * z) / pow2 64} ->
  Lemma
    (result < getPrime c * getPrime c)


let montgomery_multiplication_one_round_proof_border #c z t result  = 
  let prime = getPrime c in 
  lemma_mult_lt_right prime z (pow2 64)


val montgomery_multiplication_one_round_proof_w_ko: 
  #c: curve {(getPrime c + 1) % pow2 64 == 0} ->
  t: nat {t < getPrime c * getPrime c} -> 
  result: nat {result = (t + getPrime c * (t % pow2 64)) / pow2 64} ->
  co: nat {co % getPrime c == t % getPrime c} -> 
  Lemma (
    result % getPrime c == co * modp_inv2 #c (pow2 64) % getPrime c)


let montgomery_multiplication_one_round_proof_w_ko #c t result co = 
  let prime = getPrime c in 
  mult_one_round #c t co; 
  mul_lemma_1 (t % pow2 64) (pow2 64) prime; 
  
  lemma_mult_lt_sqr prime prime (getPower2 c);
  lemma_mult_lt_left (pow2 64) prime (getPower2 c);
  lemma_add_lt (prime * prime) (pow2 64 * prime) (getPower2 c * getPower2 c) (pow2 64 * getPower2 c)


val lemma_mod_inv: #c: curve ->  t: int -> Lemma (t % getPrime c = t * modp_inv2 #c (pow2 0) % getPrime c)

let lemma_mod_inv #c t = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime 1 (prime - 2);
  power_one (prime - 2)


val lemma_inv1: a: int -> b: int{a < b} -> Lemma (a < b * b)

let lemma_inv1 a b = ()


val lemma_modp_as_pow: #c: curve -> a: nat -> Lemma
    (modp_inv2 #c a == pow (a % getPrime c) (getPrime c - 2) % getPrime c)

let lemma_modp_as_pow #c a = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime (a % prime) (prime - 2)


val lemma_multiplication_by_inverse: #c: curve -> a0: nat -> i: size_t ->
  Lemma (
    let prime = getPrime c in 
    a0 * modp_inv2 #c (pow2 (v i * 64)) * modp_inv2_prime (pow2 64) prime % prime = 
    a0 * modp_inv2 #c (pow2 ((v i + 1) * 64)) % getPrime c)


let lemma_multiplication_by_inverse #c a0 i = 
  let prime = getPrime c in 

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==) {
      a0 * modp_inv2 #c (pow2 (v i * 64)) * modp_inv2_prime (pow2 64) prime % prime;
      (==) {assert_by_tactic (a0 * modp_inv2 #c (pow2 (v i * 64)) * modp_inv2_prime (pow2 64) prime ==
      a0 * (modp_inv2 #c (pow2 (v i * 64)) * modp_inv2_prime (pow2 64) prime)) canon}
      a0 * (modp_inv2_prime (pow2 (v i * 64)) prime * modp_inv2_prime (pow2 64) prime) % prime;
      (==) {lemma_mod_mul_distr_r a0 (modp_inv2_prime (pow2 (v i * 64)) prime * modp_inv2_prime (pow2 64) prime) prime}
      a0 * (modp_inv2 #c (pow2 (v i * 64)) * modp_inv2 #c (pow2 64) % prime) % prime;
  };

  let pow2_64 = pow2 64 in 
  let i = v i in 
  calc(==)
  {
    modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c pow2_64 % prime;
    (==) {lemma_modp_as_pow #c (pow2 (i * 64)); lemma_modp_as_pow #c pow2_64}
    (pow (pow2_64 % prime) (prime - 2) % prime) * (pow (pow2 (i * 64) % prime) (prime - 2) % prime) % prime;
    (==) {power_distributivity (pow2_64) (prime - 2) prime}
    (pow (pow2_64) (prime - 2) % prime) * (pow (pow2 (i * 64) % prime) (prime - 2) % prime) % prime;
    (==) {power_distributivity (pow2 (i * 64)) (prime - 2) prime}
    (pow (pow2_64) (prime - 2) % prime) * (pow (pow2 (i * 64)) (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_l (pow (pow2_64) (prime - 2)) (pow (pow2 (i * 64)) (prime - 2) % prime) prime}
    (pow (pow2_64) (prime - 2)) * (pow (pow2 (i * 64)) (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (pow (pow2_64) (prime - 2)) (pow (pow2 (i * 64)) (prime - 2)) prime}
    (pow (pow2_64) (prime - 2)) * (pow (pow2 (i * 64)) (prime - 2)) % prime;
    (==) {power_distributivity_2 pow2_64 (pow2 (i * 64)) (prime - 2)}
    (pow (pow2_64 * pow2 (i * 64)) (prime - 2)) % prime;
    (==) {pow2_plus 64 (i * 64)}
    (pow (pow2 ((i + 1) * 64)) (prime - 2)) % prime; 
    (==) {power_distributivity (pow2 ((i + 1) * 64)) (prime - 2) prime}
    (pow (pow2 ((i + 1) * 64) % prime) (prime - 2)) % prime; 
    (==) {lemma_modp_as_pow #c (pow2 ((i + 1) * 64))}
    modp_inv2 #c (pow2 ((i + 1) * 64)); 
  }




val lemma_reduce_mod_ecdsa_prime:
  #c: curve 
  -> t: nat 
  -> k0: nat {k0 = min_one_prime (pow2 64) (- getPrime c)} ->  Lemma (
    let prime = getPrime c in 
    (t + prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == 0)
    
let lemma_reduce_mod_ecdsa_prime #c t k0 = 
  let prime = getPrime c in 

  assert_norm(exp #(pow2 64) ((- getPrime P384) % pow2 64) ( pow2 64) == 1);
  admit()


(*
  let f = prime * (k0 * (t % pow2 64) % pow2 64) in 
  let t0 = (t + f) % pow2 64 in 
  lemma_mod_add_distr t f (pow2 64);
  modulo_addition_lemma t (pow2 64) f;
  lemma_mod_mul_distr_r k0 t (pow2 64);
  lemma_mod_mul_distr_r prime (k0 * t) (pow2 64); 
    assert_by_tactic(prime * (k0 * t) == (prime * k0) * t) canon;
  lemma_mod_mul_distr_l (prime * k0) t (pow2 64); 
    assert_norm (exp #(pow2 64) 884452912994769583 (pow2 64  - 1)  = 14758798090332847183);
  lemma_mod_mul_distr_l (-1) t (pow2 64);
  lemma_mod_add_distr t (-t) (pow2 64) *)


val mult_one_round_ecdsa_prime: 
  #c: curve 
  -> t: nat 
  -> co: nat {t % getPrime c == co % getPrime c} 
  -> k0: nat {k0 = min_one_prime (pow2 64) (- getPrime c)} -> 
  Lemma (
    let prime = getPrime c in 
    let result = (t + getPrime c * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64 in 
    result % prime == (co * modp_inv2_prime (pow2 64) prime) % prime)


let mult_one_round_ecdsa_prime #c t co k0 = 
  let prime = getPrime c in 
  
  let t2 = ((k0 * (t % pow2 64)) % pow2 64) * prime in 
  let t3 = t + t2 in  

  modulo_addition_lemma t prime ((k0 * (t % pow2 64)) % pow2 64); 
  lemma_div_mod t3 (pow2 64);
  (*admit();
  lemma_reduce_mod_ecdsa_prime prime t k0;
  admit(); *)
  admit();
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
    lemma_division_is_multiplication t3 prime;
    lemma_multiplication_to_same_number t3 co (modp_inv2_prime (pow2 64) prime) prime


val lemma_multiplication_by_inverse_k0: 
    #c: curve
  -> a0: nat 
  -> a_i: nat {a_i < getPrime c * getPrime c} 
  -> a_i1: nat {a_i1 = (a_i + getPrime c * ((v (getKo c) * (a_i % pow2 64)) % pow2 64)) / pow2 64} 
  -> i: nat {i < uint_v (getCoordinateLenU64 c)} -> 
  Lemma 
    (requires (a_i % getPrime c = a0 * modp_inv2 #c (pow2 (i * 64)) % getPrime c))
    (ensures (a_i1 % getPrime c = a0 * modp_inv2 #c (pow2 ((i + 1) * 64)) % getPrime c))


let lemma_multiplication_by_inverse_k0 #c a0 a_i a_i1 i = 
  assert(a_i % getPrime c == a0 * modp_inv2 #c (pow2 (i * 64)) % getPrime c);
  assert(a_i1 =  (a_i + getPrime c * ((v (getKo c) * (a_i % pow2 64)) % pow2 64)) / pow2 64);

  assert(v (getKo c) = min_one_prime (pow2 64) (- getPrime c));

  admit()

