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

open Lib.Sequence

val lemma_mod_inv: #c: curve ->  t: int -> Lemma (t % getPrime c = t * modp_inv2 #c (pow2 0) % getPrime c)

let lemma_mod_inv #c t = 
  let prime = getPrime c in 
  lemma_pow_mod_n_is_fpow prime 1 (prime - 2);
  power_one (prime - 2)


(* Used onlyECDSA.MontgomeryMult - to delete *)
val mult_one_round_ecdsa_prime: 
  #c: curve 
  -> t: nat 
  -> co: nat {t % getPrime c == co % getPrime c} 
  -> k0: nat {k0 = min_one_prime (pow2 64) (- getPrime c)} -> 
  Lemma (
    let prime = getPrime c in 
    let result = (t + getPrime c * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64 in 
    result % prime == (co * modp_inv2_prime (pow2 64) prime) % prime)


let mult_one_round_ecdsa_prime #c t co k0 = admit()


val lemma_test: #l: size_nat -> c: curve ->  a: lseq uint64 l -> i: nat {i <= l} 
  -> Lemma (ensures (
    let a0 = sub a 0 i in 
    let a1 = sub a i (l - i) in 
    lseq_as_nat a = lseq_as_nat a0 + pow2 (64 * i) * lseq_as_nat a1))
    (decreases (l - i))

let rec lemma_test #l c a i = 
  if i = 0 then begin 
    let a0 = sub a 0 0 in 
    let a1 = sub a 0 l in 
    lseq_as_nat_last a0
    end
  else begin if i = l then lseq_as_nat_last (sub a l 0) else
    begin 
      let a0 = sub a 0 i in 
      let a1 = sub a i (l - i) in 

      calc (==) 
      {
  lseq_as_nat a1;
  (==) {lemma_test #(l - i) c a1 1}
  lseq_as_nat (sub a1 0 1) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
  (==) {lseq_as_nat_first (sub a1 0 1)}
  v (index a1 0) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
  (==) {Seq.lemma_index_slice a 0 (i + 1) i}
  v (index a i) + pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      };
    
    assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));

    lemma_lseq_as_seq_extension (sub a 0 (i + 1)) (sub a 0 i) i;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    
    calc (==) {
      lseq_as_nat a;
      (==) {lemma_test c a (i + 1)}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * (i + 1)) * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) { pow2_plus (64 * i) 64}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) {assert_by_tactic (pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a  (i + 1) (l - (i + 1))) == 
  pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))) canon}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));
      (==) {assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))}
      lseq_as_nat (sub a 0 (i + 1)) - pow2 (64 * i) * v (index a i) + pow2 (64 * i) * lseq_as_nat a1; 
      (==) {assert (lseq_as_nat (sub a 0 (i + 1)) == lseq_as_nat (sub a 0 i) + pow2 (64 * i) * v (index a i))}
      lseq_as_nat (sub a 0 i) + pow2 (64 * i) * lseq_as_nat a1;}
    end end



open FStar.Math.Euclid 
open FStar.Math.Fermat


#push-options "--z3rlimit 100 --ifuel 0 --fuel 0"

val lemma_division_is_multiplication:
  t3: nat{t3 % pow2 64 = 0} ->
  prime: pos {is_prime prime /\ prime > 3 /\ prime > pow2 64} -> 
  Lemma (t3 * modp_inv2_prime (pow2 64) prime % prime = (t3 / pow2 64) % prime)

let lemma_division_is_multiplication t3 prime =  

  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) (prime - 2);
  lemma_mod_twice (Spec.P256.pow (pow2 64 % prime) (prime - 2)) prime;

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==) {t3 * modp_inv2_prime (pow2 64) prime % prime;
    (==) {FStar.Math.Lib.lemma_div_def t3 (pow2 64)}
     pow2 64 * (t3 / pow2 64) * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime;
    (==) {assert_by_tactic (pow2 64 * (t3 / pow2 64) * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime == 
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) % prime) canon}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (t3 / pow2 64) (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime)) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64 % prime) (prime - 2) % prime) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_distributivity (pow2 64) (prime - 2) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64) (prime - 2) % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (pow2 64) (Spec.P256.pow (pow2 64) (prime - 2)) prime}
    (t3 / pow2 64) * (pow2 64 * (Spec.P256.pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {Hacl.Lemmas.P256.power_one_2 (pow2 64)}
    (t3 / pow2 64) * (Spec.P256.pow (pow2 64) 1 * (Spec.P256.pow (pow2 64) (prime - 2)) % prime) % prime;
    (==) {pow_plus (pow2 64) 1 (prime - 2)}
    (t3 / pow2 64) * ((Spec.P256.pow (pow2 64) (prime - 1)) % prime) % prime;
    (==) {  FStar.Math.Fermat.fermat_alt prime (pow2 64);
      power_as_specification_same_as_fermat (pow2 64) (prime - 1)}
    (t3 / pow2 64) % prime;
  }





val lemma_k0_computation: #c: curve-> t: nat -> k0 : uint64 {k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c)} ->
  Lemma (let prime = getPrime c in  (t + prime * (((t % pow2 64) * v k0) % pow2 64)) % pow2 64 == 0)

let lemma_k0_computation #c t k0 = 
  let prime = getPrime c in 
  let n0 = getLastWord #c in 

  Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWord #c);

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
  t: nat ->
  k0 : uint64 {k0 == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWord #c)} ->
  round: nat {round = (t + getPrime c * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64} -> 
  co: nat {co % getPrime c = t % getPrime c} -> 
  Lemma (round  % getPrime c == co * (modp_inv2_prime (pow2 64) (getPrime c)) % ( getPrime c ))

let montgomery_multiplication_one_round_proof #c t k0 round co =
  let prime = getPrime c in 
  let round = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 in 
  assert(round % prime = (t + prime * (((t % pow2 64) * v k0) % pow2 64)) / pow2 64 % prime);

  let k = t + prime * (((t % pow2 64) * v k0) % pow2 64) in 

  lemma_k0_computation #c t k0;
  assume (is_prime prime /\ prime > pow2 64);
  lemma_division_is_multiplication k prime;

  modulo_addition_lemma t prime (((t % pow2 64) * v k0) % pow2 64);

  lemma_mod_mul_distr_l k (modp_inv2_prime (pow2 64) prime) prime;
  lemma_mod_mul_distr_l co (modp_inv2_prime (pow2 64) prime) prime






val lemma_up_bound0: #c: curve -> t0: nat {t0 < getPrime c * pow2 (64 * v (getCoordinateLenU64 c))} 
  -> t: nat{let prime = getPrime c in t <= t0 / (pow2 (64 * v (getCoordinateLenU64 c))) + prime} -> 
  Lemma (t < 2 * (getPrime c))

let lemma_up_bound0 #c t0 t = 
  let prime = getPrime c in 
  let s = pow2 (64 * v (getCoordinateLenU64 c)) in 
  lemma_mult_lt_left prime prime s;
  assert(t0 < prime * s);
  assert(t0 / s < prime);

  assert(t < prime + prime)


val lemma_up_bound1: #c: curve -> i: nat {i < v (getCoordinateLenU64 c)} 
  -> t: nat {t < getPrime c * pow2 (64 * v (getCoordinateLenU64 c))}  
  -> t0: nat {let prime = getPrime c in t0 <= t / (pow2 (64 * i)) + prime} 
  -> k0: nat {k0 < pow2 64} 
  -> t1: nat {t1 = (t0 + getPrime c * (((t0 % pow2 64) * k0) % pow2 64)) / pow2 64} -> 
  Lemma (let prime = getPrime c in t1 <= t / (pow2 (64 * (i + 1))) + prime)

let lemma_up_bound1 #c i t t0 k0 t1= 
  let prime = getPrime c in 
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

val lemma_mm_reduction: #c: curve -> a0: nat -> i: nat -> Lemma
  (let prime = getPrime c in 
    a0 * modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64) % prime == a0 * modp_inv2 #c (pow2 ((i + 1) * 64)) % prime)

let lemma_mm_reduction #c a0 i = 
  let open Spec.P256 in 
  let prime = getPrime c in 
  
  let a = pow2 (i * 64) in 

  let exp_prime: pos = prime - 2 in 

  assert(modp_inv2 #c a == exp #prime (a % prime) exp_prime % prime);
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (a % prime) exp_prime;
  lemma_mod_twice (pow (a % prime) exp_prime) prime;

  assert(modp_inv2 #c (pow2 64) == exp #prime (pow2 64 % prime) exp_prime % prime);
  Hacl.Lemmas.P256.lemma_pow_mod_n_is_fpow prime (pow2 64 % prime) exp_prime;
  lemma_mod_twice (pow (pow2 64 % prime) exp_prime) prime;

  Hacl.Lemmas.P256.power_distributivity_2 (a % prime) (pow2 64 % prime) exp_prime;


  lemma_mod_mul_distr_r a0 (modp_inv2 #c a * modp_inv2 #c (pow2 64)) prime;

  calc (==) {
    modp_inv2 #c a * modp_inv2 #c (pow2 64) % prime;
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
    modp_inv2 #c (a * pow2 64);
    (==) {pow2_plus (i * 64) 64}
    modp_inv2 #c (pow2 ((i + 1) * 64));};

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (a0 * modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64) % prime == a0 * (modp_inv2 #c (pow2 (i * 64)) * modp_inv2 #c (pow2 64)) % prime) canon

#pop-options





val lemma_mult_lt_center: a: nat -> b: nat -> c: pos -> d: pos -> Lemma
    (requires (a < c /\ b < d))
    (ensures (a * b < c * d))

let lemma_mult_lt_center a b c d = ()


val lemma_domain: #c: curve -> a: nat {a < getPrime c} -> b: nat {b < getPrime c} ->  k: nat ->
  Lemma 
    (requires (k == (a *  b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c))
    (ensures (
      k == toDomain_ #c (fromDomain_ #c a * fromDomain_ #c b % getPrime c) /\
      k == toDomain_ #c (fromDomain_ #c a * fromDomain_ #c b)))

let lemma_domain #c a b k = 
  let prime = getPrime c in 
  let multResult = a * b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 

  let mod = modp_inv2_prime (pow2 (getPower c)) prime in 
  
  calc (==) {
    a * b * mod % prime;
    (==) {lemmaFromDomainToDomain #c multResult}
    toDomain_ #c (fromDomain_ #c multResult);
    (==) {lemmaFromDomain #c multResult}
    toDomain_ #c ((a * b * mod  % prime) * mod % prime);
    (==) {lemma_mod_mul_distr_l (a * b * mod) mod prime}
    toDomain_ #c (a * b * mod * mod % prime);
    (==) {
      let open FStar.Tactics in 
      let open FStar.Tactics.Canon in 
      assert_by_tactic (a * b * mod * mod == (a * mod) * (b * mod)) canon}
    toDomain_ #c ((a * mod) * (b * mod) % prime);
    (==) {
      lemma_mod_mul_distr_l (a * mod) (b *  mod) prime; 
      lemma_mod_mul_distr_r (a * mod % prime) (b * mod) prime}
      
    toDomain_ #c ((a * mod % prime) * (b * mod % prime) % prime);
    (==) {lemmaFromDomain #c a; lemmaFromDomain #c b}
    toDomain_ #c (fromDomain_ #c a * fromDomain_ #c b % prime);};

    inDomain_mod_is_not_mod #c (fromDomain_ #c a * fromDomain_ #c b)
