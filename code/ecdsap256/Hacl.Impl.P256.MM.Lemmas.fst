module Hacl.Impl.P256.MM.Lemmas

open FStar.Math.Lemmas
open FStar.Mul
open Spec.P256.Definitions
open Spec.P256.Lemmas

open FStar.Tactics 
open FStar.Tactics.Canon 


#set-options "--z3rlimit 300"

val lemma_exp_1_0: t0D: nat -> t1D: nat -> Lemma
  (pow (pow t0D (pow2 10) * pow t1D 2 % prime256) (pow2 9) % prime256 = 
  pow t0D (pow2 19) * pow t1D (pow2 10) % prime256)

let lemma_exp_1_0 t0D t1D =  

  let pow2_9 = pow2 9 in 
  let pow2_10 = pow2 10 in 
  let pow2_19 = pow2 19 in 

  calc (==) {pow (pow t0D (pow2 10) * pow t1D 2 % prime256) (pow2 9) % prime256;
    (==) {power_distributivity (pow t0D (2 * pow2 9) * pow t1D 2) (pow2 9) prime256}
  pow (pow t0D (pow2 10) * pow t1D 2) (pow2 9) % prime256;
    (==) {power_distributivity_2 (pow t0D (pow2 10)) (pow t1D 2) (pow2 9)}
  pow (pow t0D (pow2 10)) (pow2 9) * pow (pow t1D 2) (pow2 9) % prime256;  
    (==) {power_mult t0D (pow2 10) (pow2 9)}
  pow t0D (pow2_9 * pow2_10) * pow (pow t1D 2) (pow2 9) % prime256;   
    (==) {pow2_plus 9 10}
  pow t0D (pow2_19) * pow (pow t1D 2) (pow2 9) % prime256;
    (==) {power_mult t1D 2 (pow2 9)}
  pow t0D (pow2_19) * pow t1D (2 *  (pow2 9)) % prime256;
    (==) {pow2_double_mult 9}
  pow t0D (pow2_19) * pow t1D (pow2 10) % prime256;
  }


val lemma_exp_1_1: t0D: nat -> t1D: nat -> Lemma (
  pow t0D (pow2 19) * pow t1D (pow2 10) % prime256 * pow t1D 1 % prime256 == 
  pow t0D (pow2 19) * pow t1D (pow2 10 + 1) % prime256)

let lemma_exp_1_1 t0D t1D = 
  let pow2_19 = pow2 19 in 
  calc (==) {
    pow t0D (pow2_19) * pow t1D (pow2 10) % prime256 * pow t1D 1 % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_19 * pow t1D (pow2 10)) (pow t1D 1) prime256}
    pow t0D (pow2_19) * pow t1D (pow2 10) * pow t1D 1 % prime256;
    (==) {assert_by_tactic (pow t0D (pow2_19) * pow t1D (pow2 10) * pow t1D 1 == pow t0D (pow2_19) * (pow t1D (pow2 10) * pow t1D 1)) canon}
    pow t0D (pow2_19) * (pow t1D (pow2 10) * pow t1D 1) % prime256;
    (==) {pow_plus t1D (pow2 10) 1}
    pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256;
  }


val lemma_exp_1_2: t0D: nat -> t1D: nat -> Lemma (
  pow t0D (pow2 19) * pow t1D (pow2 10 + 1) % prime256 * (pow t0D (pow2 19) * pow t1D (pow2 10 + 1) % prime256) % prime256 == 
  pow t0D (pow2 20) * pow t1D (pow2 11 + 2) % prime256)

let lemma_exp_1_2 t0D t1D = 
  let pow2_19 = pow2 19 in 
  let pow2_20 = pow2 20 in 
  let pow2_10 = pow2 10 in 
  

  calc (==) {
    pow t0D pow2_19 * pow t1D (pow2 10 + 1) % prime256 * (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256) % prime256;
  (==) {lemma_mod_mul_distr_l (pow t0D (pow2_19) * pow t1D (pow2 10 + 1)) (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256) prime256}
    pow t0D (pow2_19) * pow t1D (pow2 10 + 1) * (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256) % prime256;
  (==) {lemma_mod_mul_distr_r (pow t0D (pow2_19) * pow t1D (pow2 10 + 1)) (pow t0D (pow2_19) * pow t1D (pow2 10 + 1)) prime256}
    pow t0D (pow2_19) * pow t1D (pow2 10 + 1) * (pow t0D (pow2_19) * pow t1D (pow2 10 + 1)) % prime256;
  (==) {assert_by_tactic (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) * (pow t0D (pow2_19) * pow t1D (pow2 10 + 1)) ==
    (pow t0D pow2_19 * pow t0D pow2_19 * (pow t1D (pow2 10 + 1) * pow t1D (pow2 10 + 1)))) canon}
  pow t0D pow2_19 * pow t0D pow2_19 * (pow t1D (pow2 10 + 1) * pow t1D (pow2 10 + 1)) % prime256;
    (==) {pow_plus t0D pow2_19 pow2_19}
  pow t0D (pow2_19 + pow2_19) * (pow t1D (pow2 10 + 1) * pow t1D (pow2 10 + 1)) % prime256; 
    (==) {pow_plus t1D (pow2 10 + 1) (pow2 10 + 1)}
  pow t0D (2 * pow2_19) * (pow t1D (2* pow2 10 + 2)) % prime256;  
    (==) {pow2_double_sum 19}
  pow t0D pow2_20 * (pow t1D (2 * pow2 10 + 2)) % prime256;
    (==) {pow2_double_sum 10}
  pow t0D pow2_20 * (pow t1D (pow2 11 + 2)) % prime256;
  }


val lemma_exp_1_3: t0D: nat -> t1D: nat -> Lemma (
  (pow t0D (pow2 20) * pow t1D (pow2 11 + 2) % prime256 * (pow t0D (pow2 20) * pow t1D (pow2 11 + 2) % prime256) % prime256) == 
  pow t0D (pow2 21) * pow t1D (pow2 12 + 4) % prime256)

let lemma_exp_1_3 t0D t1D = 
  let pow2_20 = pow2 20 in 
  let pow2_21 = pow2 21 in 

  let a = pow t0D pow2_20 in 
  let b = pow t1D (pow2 11 + 2) in 
  
  calc (==) { 
  a * b % prime256 * (a * b % prime256) % prime256;
    (==) {lemma_mod_mul_distr_l (a * b) (a * b % prime256) prime256}
  a * b * (a * b % prime256) % prime256;
    (==) {lemma_mod_mul_distr_r (a * b) (a * b) prime256}
   a * b * (a * b) % prime256;
   (==) {assert_by_tactic (a * b * (a * b) == (a * a) * (b * b)) canon}
   (a * a) * (b * b) % prime256; 
   (==) {pow_plus t0D pow2_20 pow2_20; pow_plus t1D (pow2 11 + 2) (pow2 11 + 2)}
   pow t0D (2 * pow2_20) * (pow t1D (2 * pow2 11 + 4)) % prime256;
   (==) {pow2_double_sum 20; pow2_double_sum 11}
   pow t0D pow2_21 * pow t1D (pow2 12 + 4) % prime256;}


val lemma_exp_1_4: t0D: nat -> t1D: nat -> t2D: nat -> Lemma (
  pow t0D (pow2 21) * pow t1D (pow2 12 + 4) % prime256 * t2D % prime256 ==
  pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256)

let lemma_exp_1_4 t0D t1D t2D =
  let pow2_21 = pow2 21 in 

  calc (==) {pow t0D (pow2_21) * pow t1D (pow2 12 + 4) % prime256 * t2D % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_21 * pow t1D (pow2 12 + 4)) t2D prime256}
  pow t0D (pow2_21) * pow t1D (pow2 12 + 4) * t2D % prime256;
  }

val lemma_exp_1_5: t0D: nat -> t1D: nat -> t2D: nat -> Lemma (
  (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256 * (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256) % prime256 == 
  pow t0D (pow2 22) * pow t1D (pow2 13 + 8) * pow t2D 2 % prime256))

let lemma_exp_1_5 t0D t1D t2D = 
  let pow2_21 = pow2 21 in 
  let pow2_22 = pow2 22 in 

  let a = pow t0D pow2_21 in 
  let b = pow t1D (pow2 12 + 4) in 
  let c = pow t2D 1 in 

  calc (==) {a * b * c % prime256 * (a * b * c % prime256) % prime256;
    (==) {lemma_mod_mul_distr_l (a * b * c) (a * b * c % prime256) prime256}
  a * b * c * (a * b * c % prime256) % prime256;
    (==) {lemma_mod_mul_distr_r (a * b * c) (a * b * c) prime256}
  a * b * c * (a * b * c) % prime256;
    (==) {assert_by_tactic (a * b * c * (a * b * c) % prime256 == (a * a) * (b * b) * (c * c) % prime256) canon}
  (a * a) * (b * b) * (c * c) % prime256;
    (==) {pow_plus t0D pow2_21 pow2_21; pow_plus t1D (pow2 12 + 4) (pow2 12 + 4); pow_plus t2D 1 1}
  pow t0D (2 * pow2_21) * pow t1D (2 * pow2 12 + 8) * pow t2D 2 % prime256;  
    (==) {pow2_double_sum 21; pow2_double_sum 12}
  pow t0D pow2_22 * pow t1D (pow2 13 + 8) * pow t2D 2 % prime256;   
  }



val lemma_exp_1_6: t0D : nat -> t1D: nat -> t2D: nat -> Lemma (
  pow (pow t0D (pow2 22) * pow t1D (pow2 13 + 8) * pow t2D 2 % prime256) (pow2 31) % prime256 == 
  pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) % prime256)

let lemma_exp_1_6 t0D t1D t2D = 

  assert_norm (pow2 3 == 8);
  
  let pow2_22 = pow2 22 in 
  let pow2_31 = pow2 31 in 
  let pow2_32 = pow2 32 in 
  let pow2_53 = pow2 53 in 
  let pow2_44 = pow2 44 in 
  let pow2_34 = pow2 34 in 
  

  let a = pow t0D (pow2 22) in 
  let b = pow t1D (pow2 13 + 8) in 
  let c = pow t2D 2 in 
  
  calc (==) {
    pow (a * b * c % prime256) pow2_31 % prime256;
    (==) {power_distributivity (a * b * c) pow2_31 prime256}
    pow (a * b * c) pow2_31 % prime256; 
    (==) {power_distributivity_2 a (b * c) pow2_31}
    pow a pow2_31 * pow (b * c) pow2_31 % prime256;
    (==) {power_distributivity_2 b c pow2_31}
    pow a pow2_31 * (pow b pow2_31 * pow c pow2_31) % prime256;
    (==) {power_mult t0D pow2_22 pow2_31; power_mult t1D (pow2 13 + 8) pow2_31; power_mult t2D 2 pow2_31}
    pow t0D (pow2_22 * pow2_31) * (pow t1D (pow2 13 * pow2_31 + pow2 3 * pow2_31) * pow t2D (2 * pow2_31)) % prime256;
    (==) {pow2_plus 22 31; pow2_plus 13 31; pow2_plus 3 31}
    pow t0D pow2_53 * (pow t1D (pow2_44 + pow2_34) * pow t2D (2 * pow2_31)) % prime256;
    (==) {pow2_double_mult 31}
    pow t0D pow2_53 * (pow t1D (pow2_44 + pow2_34) * pow t2D pow2_32) % prime256;
    (==) {assert_by_tactic (pow t0D pow2_53 * (pow t1D (pow2_44 + pow2_34) * pow t2D pow2_32) == 
      pow t0D pow2_53 * pow t1D (pow2_44 + pow2_34) * pow t2D pow2_32) canon}
    pow t0D pow2_53 * pow t1D (pow2_44 + pow2_34) * pow t2D pow2_32 % prime256; }


val lemma_exp_1_7_0: a: nat -> b: nat -> c: nat -> tD: nat -> Lemma 
  (pow (a * b * c * tD % prime256) (pow2 128) % prime256 == 
    pow a (pow2 128) * pow b (pow2 128) * pow c (pow2 128) * pow tD (pow2 128) % prime256)

let lemma_exp_1_7_0 a b c tD = 
  let pow2_128 = pow2 128 in 
 
  calc (==) {pow (a * b * c * tD % prime256) pow2_128 % prime256;
  (==) {power_distributivity (a * b * c * tD) pow2_128 prime256}
  pow (a * b * c * tD) pow2_128 % prime256; 
  (==) {power_distributivity_2 a (b * c * tD) pow2_128}
  pow a pow2_128 * pow (b * c * tD) pow2_128 % prime256;
  (==) {assert_by_tactic (b * c * tD == b * (c * tD)) canon}
  pow a pow2_128 * pow (b * (c * tD)) pow2_128 % prime256; 
  (==) {power_distributivity_2 b (c * tD) pow2_128}
  pow a pow2_128 * (pow b pow2_128 * pow (c * tD) pow2_128) % prime256;};
  
  power_distributivity_2 c tD pow2_128;
  
  assert_by_tactic (pow a pow2_128 * (pow b pow2_128 * (pow c pow2_128 * pow tD pow2_128)) == 
   pow a pow2_128 * pow b pow2_128 * pow c pow2_128 * pow tD pow2_128) canon;

  
  assert(pow a pow2_128 * (pow b pow2_128 * pow (c * tD) pow2_128) % prime256 == 
     pow a pow2_128 * pow b pow2_128 * pow c pow2_128 * pow tD pow2_128 % prime256)



val lemma_exp_1_7: tD: nat -> t0D: nat -> t1D: nat -> t2D: nat -> Lemma (
  pow (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) * tD % prime256) (pow2 128) % prime256 == 
  pow t0D (pow2 181) * pow t1D (pow2 172 + pow2 162) * pow t2D (pow2 160) * pow tD (pow2 128) % prime256)



let lemma_exp_1_7 tD t0D t1D t2D = 
  let pow2_53 = pow2 53 in 
  let pow2_44 = pow2 44 in 
  let pow2_34 = pow2 34 in 
  let pow2_32 = pow2 32 in 
  let pow2_128 = pow2 128 in 
  
  let pow2_181 = pow2 181 in 
  let pow2_172 = pow2 172 in 
  let pow2_162 = pow2 162 in 
  let pow2_160 = pow2 160 in 

  assert_norm (pow2 128 == 340282366920938463463374607431768211456);
  assert_norm (pow2 53 == 9007199254740992); 
  assert_norm (pow2 44 == 17592186044416);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 34 == 17179869184);

  assert_norm (pow2_53 * pow2_128 == pow2_181);
  assert_norm (pow2_44 * pow2_128 == pow2_172);
  assert_norm (pow2_34 * pow2_128 == pow2_162);
  assert_norm (pow2_32 * pow2_128 == pow2_160);
 

  let a = pow t0D (pow2 53) in 
  let b = pow t1D (pow2 44 + pow2 34) in 
  let c = pow t2D (pow2 32) in

  lemma_exp_1_7_0 a b c tD;
  
  calc (==) {pow a (pow2_128);
    (==) {}
    pow (pow t0D (pow2 53)) (pow2_128); 
    (==) {power_mult t0D (pow2 53) (pow2_128)}
    pow t0D pow2_181;};

  calc (==) {pow b (pow2_128);
    (==) {}
    pow (pow t1D (pow2 44 + pow2 34)) (pow2_128);
    (==) {power_mult t1D (pow2 44 + pow2 34) (pow2_128)}
    pow t1D (pow2_172 + pow2_162);};
    
 calc (==) {pow c pow2_128;
   (==) {}
   pow (pow t2D (pow2 32)) (pow2_128); 
   (==) {power_mult t2D (pow2 32) (pow2_128)}
   pow t2D (pow2_160);}
