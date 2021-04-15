module Hacl.Impl.EC.MontgomeryMultiplication.Lemmas

open Lib.IntTypes

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Lemmas.P256
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.EC.Setup
open Hacl.Spec.EC.Definition


#set-options "--z3rlimit 200 --ifuel 0 --fuel 0"

open Lib.Sequence

val lemma_mod_inv: #c: curve -> t: int -> Lemma (t % getPrime c = t * modp_inv2 #c (pow2 0) % getPrime c)

let lemma_mod_inv #c t = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime 1 (prime - 2);
  power_one (prime - 2)

val lemma_division_is_multiplication:
  t3: nat {t3 % pow2 64 = 0} -> 
  prime: pos {FStar.Math.Euclid.is_prime prime /\ prime > 3 /\ prime > pow2 64} -> 
  Lemma (t3 * modp_inv2_prime (pow2 64) prime % prime = (t3 / pow2 64) % prime)

let lemma_division_is_multiplication t3 prime =  

  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) (prime - 2);
  lemma_mod_twice (pow (pow2 64 % prime) (prime - 2)) prime;

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==) {t3 * modp_inv2_prime (pow2 64) prime % prime;
    (==) {FStar.Math.Lib.lemma_div_def t3 (pow2 64)}
     pow2 64 * (t3 / pow2 64) * (pow (pow2 64 % prime) (prime - 2) % prime) % prime;
    (==) {assert_by_tactic (pow2 64 * (t3 / pow2 64) * (pow (pow2 64 % prime) (prime - 2) % prime) % prime == 
    (t3 / pow2 64) * (pow2 64 * (pow (pow2 64 % prime) (prime - 2) % prime)) % prime) canon}
    (t3 / pow2 64) * (pow2 64 * (pow (pow2 64 % prime) (prime - 2) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (t3 / pow2 64) (pow2 64 * (pow (pow2 64 % prime) (prime - 2) % prime)) prime}
    (t3 / pow2 64) * (pow2 64 * (pow (pow2 64 % prime) (prime - 2) % prime) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_distributivity (pow2 64) (prime - 2) prime}
    (t3 / pow2 64) * (pow2 64 * (pow (pow2 64) (prime - 2) % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (pow2 64) (pow (pow2 64) (prime - 2)) prime}
    (t3 / pow2 64) * (pow2 64 * (pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_one_2 (pow2 64)}
    (t3 / pow2 64) * (pow (pow2 64) 1 * (pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {pow_plus (pow2 64) 1 (prime - 2)}
    (t3 / pow2 64) * ((pow (pow2 64) (prime - 1)) % prime) % prime;
    (==) {  FStar.Math.Fermat.fermat_alt prime (pow2 64);
      power_as_specification_same_as_fermat (pow2 64) (prime - 1)}
    (t3 / pow2 64) % prime;
  }


#set-options "--z3rlimit 500 --ifuel 1 --fuel 1"


val lemma_k0_computation: #c: curve-> #m: mode -> t: nat -> 
  k0 : uint64 {match m with 
    |DH -> k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)
    |DSA -> k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c)} ->
  Lemma (let prime = getModePrime m c in (t + prime * (((t % pow2 64) * v k0) % pow2 64)) % pow2 64 == 0)

let lemma_k0_computation #c #m t k0 = 
  let prime = getModePrime m c in 
  let n0 = getLastWordPrime #c in 

  Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWordPrime #c);
  Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWordOrder #c);
  
  let k = t + prime * (((t % pow2 64) * v k0) % pow2 64) in  
  lemma_mod_mul_distr_l t (v k0) (pow2 64);
  lemma_mod_add_distr t (prime * (t * v k0 % pow2 64)) (pow2 64);
  lemma_mod_mul_distr_r prime (t * v k0) (pow2 64);
  
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (prime * (t * v k0) == t * (prime * v k0)) canon;

  assert(k % pow2 64 == (t + t * (prime * v k0) % pow2 64) % pow2 64);

  lemma_mod_mul_distr_r t (prime * v k0) (pow2 64);
  lemma_mod_mul_distr_l prime (v k0) (pow2 64);

  assert(k % pow2 64 == (t + t * ((-1 + (1 + prime % pow2 64 * v k0)) % pow2 64) % pow2 64) % pow2 64);

  lemma_mod_add_distr (-1) (1 + (prime) % pow2 64 * v k0) (pow2 64); 
  lemma_mod_mul_distr_r t (-1) (pow2 64);
  lemma_mod_add_distr t (t * (-1)) (pow2 64);
  
  assert(k % pow2 64 == 0) 


val montgomery_multiplication_one_round_proof: 
  #c: curve ->
  #m: mode ->
  t: nat ->
  k0 : uint64 {
    match m with 
    |DH -> k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)
    |DSA -> k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordOrder #c)} ->
  round: nat {round = (t + getModePrime m c * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64} -> 
  co: nat {co % getModePrime m c = t % getModePrime m c} -> 
  Lemma (round  % getModePrime m c == co * (modp_inv2_prime (pow2 64) (getModePrime m c)) % getModePrime m c)

let montgomery_multiplication_one_round_proof #c #m t k0 round co =
  let prime = getModePrime m c in 
  let round = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 in 
  assert(round % prime = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 % prime);

  let k = t + prime * (((t % pow2 64) * v k0) % pow2 64) in 

  lemma_k0_computation #c #m t k0; 
  lemma_division_is_multiplication k prime; 

  modulo_addition_lemma t prime (((t % pow2 64) * v k0) % pow2 64); 

  lemma_mod_mul_distr_l k (modp_inv2_prime (pow2 64) prime) prime;
  lemma_mod_mul_distr_l co (modp_inv2_prime (pow2 64) prime) prime


val lemma_up_bound0: #c: curve -> #m: mode 
  -> t0: nat {t0 < getModePrime m c * pow2 (64 * v (getCoordinateLenU64 c))} 
  -> t: nat{let prime = getModePrime m c in t <= t0 / (pow2 (64 * v (getCoordinateLenU64 c))) + prime} -> 
  Lemma (t < 2 * (getModePrime m c))

let lemma_up_bound0 #c #m t0 t = 
  let prime = getModePrime m c in 
  let s = pow2 (64 * v (getCoordinateLenU64 c)) in 
  assert(getPower c == v (getCoordinateLenU64 c) * 64);
  assert(prime < pow2 (v (getCoordinateLenU64 c) * 64));
  lemma_mult_lt_left prime prime s;
  assert(t0 < prime * s);
  assert(t0 / s < prime);

  assert(t < prime + prime)


val lemma_up_bound1: #c: curve -> #m: mode -> i: nat {i < v (getCoordinateLenU64 c)} 
  -> t: nat {t < getModePrime m c * pow2 (64 * v (getCoordinateLenU64 c))}  
  -> t0: nat {let prime = getModePrime m c in t0 <= t / (pow2 (64 * i)) + prime} 
  -> k0: nat {k0 < pow2 64} 
  -> t1: nat {t1 = (t0 + getModePrime m c * (((t0 % pow2 64) * k0) % pow2 64)) / pow2 64} -> 
  Lemma (let prime = getModePrime m c in t1 <= t / (pow2 (64 * (i + 1))) + prime)

let lemma_up_bound1 #c #m i t t0 k0 t1= 
  let prime = getModePrime m c in 
  assert(t0 <= t / (pow2 (64 * i)) + prime); 
  assert(t1 = (t0 + prime * (((t0 % pow2 64) * k0) % pow2 64)) / pow2 64);
  assert(((t0 % pow2 64) * k0) % pow2 64 <= pow2 64 - 1);
  lemma_mult_le_left prime (((t0 % pow2 64) * k0) % pow2 64) (pow2 64 - 1);
  assert(t1 <= (t0 + prime * (pow2 64 - 1)) / pow2 64);
  assert(t1 <= (t0 + prime * pow2 64 - prime) / pow2 64); 
  assert(t1 <= (t / (pow2 (64 * i)) / pow2 64 + prime));
  division_multiplication_lemma t (pow2 (64 * i)) (pow2 64);
  assert(t1 <= (t / (pow2 (64 * i) * pow2 64) + prime));
  pow2_plus (64 * i) 64


#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"

val lemma_mm_reduction: #c: curve -> #m: mode -> a0: nat -> i: nat -> Lemma (
  let prime = getModePrime m c in 
  a0 * modp_inv2_prime (pow2 (i * 64)) prime * modp_inv2_prime (pow2 64) prime % prime == 
  a0 * modp_inv2_prime (pow2 ((i + 1) * 64)) prime % prime)

let lemma_mm_reduction #c #m a0 i = 
  let open Spec.ECC in 
  let prime = getModePrime m c in 
  
  let a = pow2 (i * 64) in
  let exp_prime: pos = prime - 2 in

  assert(modp_inv2_prime a prime == exp #prime (a % prime) (prime - 2));
  
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (a % prime) exp_prime;

  assert(modp_inv2_prime (pow2 64) prime == exp #prime (pow2 64 % prime) exp_prime); 
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) exp_prime;

  Hacl.Lemmas.P256.power_distributivity_2 (a % prime) (pow2 64 % prime) exp_prime;

  lemma_mod_mul_distr_r a0 (modp_inv2_prime a prime * modp_inv2_prime (pow2 64) prime) prime; 

  calc (==) {
    modp_inv2_prime a prime * modp_inv2_prime (pow2 64) prime % prime;
    (==) {}
    (pow (a % prime) exp_prime % prime * (pow (pow2 64 % prime) exp_prime % prime)) % prime; 
    (==) {lemma_mod_mul_distr_l (pow (a % prime) exp_prime) (pow (pow2 64 % prime) exp_prime % prime) prime}
    (pow (a % prime) exp_prime * (pow (pow2 64 % prime) exp_prime % prime)) % prime; 
    (==) {lemma_mod_mul_distr_r (pow (a % prime) exp_prime) (pow (pow2 64 % prime) exp_prime) prime}
    (pow (a % prime) exp_prime * pow (pow2 64 % prime) exp_prime) % prime; 
    (==) {pow_plus (a % prime) (pow2 64 % prime) exp_prime}
    (pow (a % prime * (pow2 64 % prime)) exp_prime) % prime; 
    (==) {Hacl.Lemmas.P256.power_distributivity (a % prime * (pow2 64 % prime)) exp_prime prime}
    (pow (a % prime * (pow2 64 % prime) % prime) exp_prime) % prime;  
    (==) {lemma_mod_mul_distr_l a (pow2 64 % prime) prime}
    (pow ((a * (pow2 64 % prime)) % prime) exp_prime) % prime; 
    (==) {lemma_mod_mul_distr_r a (pow2 64) prime}
    (pow ((a * pow2 64) % prime) exp_prime) % prime; 
    (==) {lemma_mod_twice (pow ((a * pow2 64) % prime) exp_prime) prime}
    ((pow ((a * pow2 64) % prime) exp_prime) % prime) % prime; 
    (==) {Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (a * pow2 64 % prime) exp_prime} 
    exp #prime ((a * pow2 64) % prime) exp_prime % prime; 
    (==) {}
    modp_inv2_prime (a * pow2 64) prime % prime; 
    (==) {small_mod (modp_inv2_prime (a * pow2 64) prime) prime}
    modp_inv2_prime (a * pow2 64) prime; 
    (==) {pow2_plus (i * 64) 64}
    modp_inv2_prime (pow2 ((i + 1) * 64)) prime; 
    };

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (a0 * modp_inv2_prime (pow2 (i * 64)) prime * modp_inv2_prime (pow2 64) prime % prime == a0 * (modp_inv2_prime (pow2 (i * 64)) prime * modp_inv2_prime (pow2 64) prime) % prime) canon

#pop-options


val lemma_mult_lt_center: a: nat -> b: nat -> c: pos -> d: pos -> Lemma
    (requires (a < c /\ b < d))
    (ensures (a * b < c * d))

let lemma_mult_lt_center a b c d = ()


val lemma_domain: #c: curve -> #m: mode -> a: nat {a < getModePrime m c} -> b: nat {b < getModePrime m c} ->  k: nat ->
  Lemma 
  (requires (k == (a *  b * modp_inv2_prime (pow2 (getPower c)) (getModePrime m c)) % getModePrime m c))
  (ensures (
    k == toDomain_ #c #m (fromDomain_ #c #m a * fromDomain_ #c #m b % getModePrime m c) /\
    k == toDomain_ #c #m (fromDomain_ #c #m a * fromDomain_ #c #m b)))

let lemma_domain #c #m a b k = 
  let prime = getModePrime m c in 
  let multResult = a * b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 

  let mod = modp_inv2_prime (pow2 (getPower c)) prime in 
  
  calc (==) {
    a * b * mod % prime;
    (==) {lemmaFromDomainToDomain #c #m multResult}
    toDomain_ #c #m (fromDomain_ #c #m multResult);
    (==) {lemmaFromDomain #c #m multResult}
    toDomain_ #c #m ((a * b * mod  % prime) * mod % prime);
    (==) {lemma_mod_mul_distr_l (a * b * mod) mod prime}
    toDomain_ #c #m (a * b * mod * mod % prime);
    (==) {
      let open FStar.Tactics in 
      let open FStar.Tactics.Canon in 
      assert_by_tactic (a * b * mod * mod == (a * mod) * (b * mod)) canon}
    toDomain_ #c #m ((a * mod) * (b * mod) % prime);
    (==) {
      lemma_mod_mul_distr_l (a * mod) (b *  mod) prime; 
      lemma_mod_mul_distr_r (a * mod % prime) (b * mod) prime}
      
    toDomain_ #c #m ((a * mod % prime) * (b * mod % prime) % prime);
    (==) {lemmaFromDomain #c #m a; lemmaFromDomain #c #m b}
    toDomain_ #c #m (fromDomain_ #c #m a * fromDomain_ #c #m b % prime);};

    inDomain_mod_is_not_mod #c #m (fromDomain_ #c #m a * fromDomain_ #c #m b)
