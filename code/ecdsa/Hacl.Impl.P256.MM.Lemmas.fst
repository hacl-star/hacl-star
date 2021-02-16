module Hacl.Impl.P256.MM.Lemmas

open FStar.Math.Lemmas
open FStar.Mul
open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256

open Spec.P256

open FStar.Tactics 
open FStar.Tactics.Canon 


#set-options "--z3rlimit 300"



val lemma_pow_sum: tD : nat -> a: nat -> b: nat -> Lemma 
  (pow tD a % prime256 * (pow tD b % prime256) % prime256 == pow tD (a + b) % prime256)

let lemma_pow_sum tD a b = 
  calc (==) {pow tD a % prime256 * (pow tD b % prime256) % prime256;
    (==) {lemma_mod_mul_distr_l (pow tD a) (pow tD b % prime256) prime256}
  pow tD a * (pow tD b % prime256) % prime256;
    (==) {lemma_mod_mul_distr_r (pow tD a) (pow tD b) prime256}
  pow tD a * (pow tD b) % prime256;
    (==) {assert_by_tactic (pow tD a * (pow tD b) == pow tD a * pow tD b) canon}
  pow tD a * pow tD b % prime256;
    (==) {pow_plus tD a b}
  pow tD (a + b) % prime256;}


val lemma_pow_sum2: t0D : nat -> t1D: nat -> a0: nat -> a1: nat -> b0: nat -> b1: nat -> Lemma (
  pow t0D a0 % prime256 * pow t1D b0 % prime256 * (pow t0D a1 % prime256 * pow t1D b1 % prime256) % prime256 == 
  pow t0D (a0 + a1) * pow t1D (b0 + b1) % prime256)

let lemma_pow_sum2 t0D t1D a0 a1 b0 b1 = 
  calc (==) {pow t0D a0 % prime256 * pow t1D b0 % prime256 * (pow t0D a1 % prime256 * pow t1D b1 % prime256) % prime256;
  (==)  {lemma_mod_mul_distr_l (pow t0D a0) (pow t1D b0) prime256; lemma_mod_mul_distr_l (pow t0D a1) (pow t1D b1) prime256}
    pow t0D a0 * pow t1D b0 % prime256 * (pow t0D a1 * pow t1D b1 % prime256) % prime256; 
  (==) {lemma_mod_mul_distr_l (pow t0D a0 * pow t1D b0) (pow t0D a1 * pow t1D b1 % prime256) prime256}
    pow t0D a0 * pow t1D b0 * (pow t0D a1 * pow t1D b1 % prime256) % prime256; 
  (==) {lemma_mod_mul_distr_r (pow t0D a0 * pow t1D b0) (pow t0D a1 * pow t1D b1) prime256}
    pow t0D a0 * pow t1D b0 * (pow t0D a1 * pow t1D b1) % prime256; 
  (==) {assert_by_tactic (pow t0D a0 * pow t1D b0 * (pow t0D a1 * pow t1D b1) == pow t0D a0 * pow t0D a1 * (pow t1D b0 * pow t1D b1)) canon}
    pow t0D a0 * pow t0D a1 * (pow t1D b0 * pow t1D b1) % prime256; 
  (==) {pow_plus t0D a0 a1; pow_plus t1D b0 b1}
    pow t0D (a0 + a1) * pow t1D (b0 + b1) % prime256;}


 val lemma_6_powers: tD: nat -> 
  Lemma ((tD * tD % prime256 * tD % prime256) * (tD * tD % prime256 * tD % prime256) % prime256 == 
    pow tD 6 % prime256)

let lemma_6_powers tD =     
    calc (==) {(tD * tD % prime256 * tD % prime256) * (tD * tD % prime256 * tD % prime256) % prime256; 
      (==) {lemma_mod_mul_distr_l (tD * tD) tD prime256}
    (tD * tD * tD % prime256) * (tD * tD * tD % prime256) % prime256;
      (==) {lemma_mod_mul_distr_l (tD * tD * tD) (tD * tD * tD % prime256) prime256}
    tD * tD * tD * (tD * tD * tD % prime256) % prime256;  
      (==) {lemma_mod_mul_distr_r (tD * tD * tD) (tD * tD * tD) prime256}
    tD * tD * tD * (tD * tD * tD) % prime256; 
      (==) {assert_by_tactic (tD * tD * tD * (tD * tD * tD) == (tD * tD) * (tD * tD) * (tD * tD)) canon}
    (tD * tD) * (tD * tD) * (tD * tD) % prime256; 
      (==) {pow_plus tD 1 1}
   pow tD 2 * pow tD 2 * pow tD 2 % prime256;
     (==) {pow_plus tD 2 2}
   pow tD 4 * pow tD 2 % prime256;
     (==) {pow_plus tD 4 2} 
   pow tD 6 % prime256;}


val lemma_15_powers: tD: nat -> 
  Lemma ((pow tD 6 % prime256 * (pow tD 6 % prime256) % prime256) * (tD * tD % prime256 * tD % prime256) % prime256 == 
    pow tD 15 % prime256)

let lemma_15_powers tD = 
    calc (==) {(pow tD 6 % prime256 * (pow tD 6 % prime256) % prime256) * (tD * tD % prime256 * tD % prime256) % prime256;
      (==) {lemma_pow_sum tD 6 6}
    (pow tD 12 % prime256) * (tD * tD % prime256 * tD % prime256) % prime256; 
      (==) {lemma_mod_mul_distr_l (pow tD 12) (tD * tD % prime256 * tD % prime256) prime256}
    pow tD 12 * (tD * tD % prime256 * tD % prime256) % prime256; 
      (==) {lemma_mod_mul_distr_l (tD * tD) tD prime256}
    pow tD 12 * (tD * tD * tD % prime256) % prime256; 
      (==) {lemma_mod_mul_distr_r (pow tD 12) (tD * tD * tD) prime256}
    pow tD 12 * (pow tD 1 * pow tD 1 * pow tD 1) % prime256;   
      (==) {assert_by_tactic (pow tD 12 * (pow tD 1 * pow tD 1 * pow tD 1) == pow tD 12 * (pow tD 1 * pow tD 1) * pow tD 1) canon}
    pow tD 12 * (pow tD 1 * pow tD 1) * pow tD 1 % prime256;   
      (==) {pow_plus tD 1 1}
    pow tD 12 * pow tD 2 * pow tD 1 % prime256;
      (==) {pow_plus tD 12 2}
    pow tD 14 * pow tD 1 % prime256;
      (==) {pow_plus tD 14 1}
    pow tD 15 % prime256;}



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


val lemma_exp_1_8: tD: nat -> t0D: nat -> t1D: nat -> t2D: nat -> Lemma (
  pow t0D (pow2 181) * pow t1D (pow2 172 + pow2 162) * pow t2D (pow2 160) * pow tD (pow2 128) % prime256 * 
    (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256) % prime256 == 
    pow t0D (pow2 181 + pow2 21) * pow t1D (pow2 172 + pow2 162 + pow2 12 + 4) * pow t2D (pow2 160 + 1) * pow tD (pow2 128) % prime256)

let lemma_exp_1_8 tD t0D t1D t2D =
  let pow2_181 = pow2 181 in 
  let pow2_172 = pow2 172 in 
  let pow2_162 = pow2 162 in 
  let pow2_160 = pow2 160 in 
  let pow2_128 = pow2 128 in 

  let pow2_21 = pow2 21 in 

  let a = pow t0D (pow2 181) in
  let b = pow t1D (pow2 172 + pow2 162) in 
  let c = pow t2D (pow2 160) in 
  let d = pow tD (pow2 128) in 

  let e = pow t0D (pow2 21) in 
  let f = pow t1D (pow2 12 + 4) in 
  let g = pow t2D 1 in 

  calc (==) {a * b * c * d % prime256 * (e * f * g % prime256) % prime256;
    (==) {lemma_mod_mul_distr_l (a * b * c * d) (e * f * g % prime256) prime256}
    a * b * c * d * (e * f * g % prime256) % prime256;
    (==) {lemma_mod_mul_distr_r (a * b * c * d) (e * f * g) prime256}
    a * b * c * d * (e * f * g) % prime256;
    (==) {assert_by_tactic (a * b * c * d * (e * f * g) == a * e * (b * f) * (c * g) * d) canon}
    a * e * (b * f) * (c * g) * d % prime256;
    (==) {}
    (pow t0D pow2_181 * pow t0D pow2_21) * 
    (pow t1D (pow2_172 + pow2_162) * pow t1D (pow2 12 + 4)) * 
    (pow t2D (pow2_160) * pow t2D 1) * pow tD pow2_128 % prime256;
    (==) {pow_plus t0D pow2_181 pow2_21; pow_plus t1D (pow2_172 + pow2_162) (pow2 12 + 4); pow_plus t2D pow2_160 1}
    pow t0D (pow2_181 + pow2_21) * pow t1D (pow2_172 + pow2_162 + pow2 12 + 4) * pow t2D (pow2_160 + 1) * pow tD pow2_128 % prime256;}


val lemma_exp_2_0: t0D: nat -> t5D: nat -> Lemma (
  pow (pow t0D (pow2 32) * t5D % prime256) (pow2 30) % prime256 == pow t0D (pow2 62) * pow t5D (pow2 30) % prime256)

let lemma_exp_2_0 t0D t5D = 
  let pow2_32 = pow2 32 in 
  let pow2_30 = pow2 30 in 
  let pow2_62 = pow2 62 in 

  calc (==) {pow (pow t0D pow2_32 * t5D % prime256) pow2_30 % prime256;
    (==) {power_distributivity (pow t0D pow2_32 * t5D) pow2_30 prime256}
  pow (pow t0D pow2_32 * t5D) pow2_30 % prime256;
    (==) {power_distributivity_2 (pow t0D pow2_32) t5D pow2_30}
  pow (pow t0D pow2_32) pow2_30 * pow t5D pow2_30 % prime256;
    (==) {power_mult t0D pow2_32 pow2_30}
  pow t0D (pow2_32 * pow2_30) * pow t5D pow2_30 % prime256;
    (==) {pow2_plus 32 30}
  pow t0D pow2_62 * pow t5D pow2_30 % prime256;}


val lemma_exp_2_1: t0D: nat -> t4D: nat -> t5D: nat -> Lemma (
  pow (pow t0D (pow2 62) * pow t5D (pow2 30) * t4D % prime256) (pow2 2) % prime256 ==  
  pow t0D (pow2 64) * pow t5D (pow2 32) * pow t4D (pow2 2) % prime256)

let lemma_exp_2_1 t0D t4D t5D = 
  let pow2_62 = pow2 62 in 
    let pow2_64 = pow2 64 in 
  let pow2_30 = pow2 30 in 
    let pow2_32 = pow2 32 in 

  calc (==) {pow (pow t0D pow2_62 * pow t5D pow2_30 * t4D % prime256) (pow2 2) % prime256;
    (==) {power_distributivity (pow t0D pow2_62 * pow t5D pow2_30 * t4D) (pow2 2) prime256}
  pow (pow t0D pow2_62 * pow t5D pow2_30 * t4D) (pow2 2) % prime256;
    (==) {assert_by_tactic (pow t0D pow2_62 * pow t5D pow2_30 * t4D == pow t0D pow2_62 * (pow t5D pow2_30 * t4D)) canon}
  pow (pow t0D pow2_62 * (pow t5D pow2_30 * t4D)) (pow2 2) % prime256;   
    (==) {power_distributivity_2 (pow t0D pow2_62) (pow t5D pow2_30 * t4D) (pow2 2)}
  pow (pow t0D pow2_62) (pow2 2) * pow (pow t5D pow2_30 * t4D) (pow2 2) % prime256;
    (==) {power_distributivity_2 (pow t5D pow2_30) t4D (pow2 2)}
   pow (pow t0D pow2_62) (pow2 2) * (pow (pow t5D pow2_30) (pow2 2) * pow t4D (pow2 2)) % prime256;  
    (==) {power_mult t0D pow2_62 (pow2 2); power_mult t5D (pow2_30) (pow2 2)}
  pow t0D (pow2_62 * pow2 2) * (pow t5D (pow2_30 * pow2 2) * pow t4D (pow2 2)) % prime256;  
    (==) {pow2_plus 62 2; pow2_plus 30 2}
  pow t0D pow2_64 * (pow t5D pow2_32 * pow t4D (pow2 2)) % prime256;    
    (==) {assert_by_tactic (pow t0D pow2_64 * (pow t5D pow2_32 * pow t4D (pow2 2)) == pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2)) canon}
  pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2) % prime256;}


val lemma_exp_0: tD: nat -> a: nat -> b: nat -> c: nat->  Lemma (
  pow (pow tD a % prime256) b * c % prime256 == pow tD (a * b) * c % prime256)


let lemma_exp_0 tD a b c = 
  calc (==) { pow (pow tD a % prime256) b * c % prime256;
    (==) {lemma_mod_mul_distr_l (pow (pow tD a % prime256) b) c prime256}
  pow (pow tD a % prime256) b % prime256 * c % prime256;
    (==) { power_distributivity (pow tD a) b prime256 }
  pow (pow tD a) b % prime256 * c % prime256;   
    (==) {lemma_mod_mul_distr_l (pow (pow tD a) b) c prime256}
  pow (pow tD a) b * c % prime256; 
    (==) {power_mult tD a b}
  pow tD (a * b) * c % prime256;   }


val lemma_exp_1: tD: nat -> Lemma (pow (pow tD 2046 % prime256) (pow2 181 + pow2 21) * pow (pow tD 1023 % prime256) (pow2 172 + pow2 162 + pow2 12 + 4) * pow (pow tD 3 % prime256) (pow2 160 + 1) * pow tD (pow2 128) % prime256  ==
  pow tD (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) % prime256)

let lemma_exp_1 tD = 
  let pow2_181 = pow2 181 in 
  let pow2_21  = pow2 21 in 
  let pow2_172 = pow2 172 in 
  let pow2_162 = pow2 162 in 
  let pow2_160 = pow2 160 in 
  let pow2_128 = pow2 128 in 

  let a = pow (pow tD 2046 % prime256) (pow2_181 + pow2_21) in 
  let b = pow (pow tD 1023 % prime256) (pow2 172 + pow2 162 + pow2 12 + 4) in 
  let c = pow (pow tD 3 % prime256) (pow2 160 + 1) in 
  let d = pow tD (pow2 128) in 

  calc (==) {a * b * c * d % prime256;
  (==) {assert_by_tactic (a * b * c * d == a * (b * c * d)) canon }
  a * (b * c * d) % prime256;
  (==) {lemma_exp_0 tD 2046 (pow2_181 + pow2 21) (b * c * d)}
  pow tD (2046 * (pow2_181 + pow2 21)) * (b * c * d) % prime256;
  (==) {assert_by_tactic (pow tD (2046 * (pow2_181 + pow2_21)) * (b * c * d) == b * (pow tD (2046 * (pow2_181 + pow2_21)) * c * d)) canon }
  b * (pow tD (2046 * (pow2_181 + pow2_21)) * c * d) % prime256;
  (==) {lemma_exp_0 tD 1023 (pow2_172 + pow2_162 + pow2 12 + 4) (pow tD (2046 * (pow2_181 + pow2_21)) * c * d)}
  pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * (pow tD (2046 * (pow2_181 + pow2_21)) * c * d) % prime256;
  (==) {assert_by_tactic (
    pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * (pow tD (2046 * (pow2_181 + pow2_21)) * c * d) == 
    c * (pow tD (2046 * (pow2_181 + pow2_21)) * pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * d)) canon}
  c * (pow tD (2046 * (pow2_181 + pow2_21)) * pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * d) % prime256;
  (==) {lemma_exp_0 tD 3 (pow2_160 + 1) (pow tD (2046 * (pow2_181 + pow2_21)) * pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * d)}
  pow tD (3 * (pow2_160 + 1)) * (pow tD (2046 * (pow2_181 + pow2_21)) * pow tD (1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * pow tD pow2_128) % prime256;
  (==) {pow_plus tD (2046 * (pow2_181 + pow2_21)) (1023 * (pow2_172 + pow2_162 + pow2 12 + 4))}
  pow tD (3 * (pow2_160 + 1)) * (pow tD (2046 * (pow2_181 + pow2_21) + 1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) * pow tD pow2_128) % prime256;
  (==) {pow_plus tD (2046 * (pow2_181 + pow2_21) + 1023 * (pow2_172 + pow2_162 + pow2 12 + 4)) pow2_128}
  pow tD (3 * (pow2_160 + 1)) * pow tD (2046 * (pow2_181 + pow2_21) + 1023 * (pow2_172 + pow2_162 + pow2 12 + 4) + pow2_128) % prime256;
  (==) {pow_plus tD (3 * (pow2_160 + 1)) (2046 * (pow2_181 + pow2_21) + 1023 * (pow2_172 + pow2_162 + pow2 12 + 4) + pow2_128)}
  pow tD (3 * (pow2_160 + 1) + 2046 * (pow2_181 + pow2_21) + 1023 * (pow2_172 + pow2_162 + pow2 12 + 4) + pow2_128) % prime256;
  }


val lemma_exp_2: tD: nat -> Lemma (pow (pow tD 2046 % prime256) (pow2 19) * pow (pow tD 1023 % prime256) (pow2 10 + 1) % prime256 ==  pow tD (1023 * (pow2 10 + 1) + 2046 * pow2 19) % prime256)

let lemma_exp_2 tD = 
  let pow2_19 = pow2 19 in 
  let pow2_10 = pow2 10 in 
  

  calc (==) {pow (pow tD 2046 % prime256) pow2_19 * pow (pow tD 1023 % prime256) (pow2_10 + 1) % prime256;
  (==) {lemma_exp_0 tD 2046 pow2_19 (pow (pow tD 1023 % prime256) (pow2_10 + 1))}
  pow tD (2046 * pow2_19) * pow (pow tD 1023 % prime256) (pow2_10 + 1) % prime256;
  (==) {assert_by_tactic (pow tD (2046 * pow2_19) * pow (pow tD 1023 % prime256) (pow2_10 + 1) == pow (pow tD 1023 % prime256) (pow2_10 + 1) * pow tD (2046 * pow2_19)) canon}
  pow (pow tD 1023 % prime256) (pow2_10 + 1) * pow tD (2046 * pow2_19) % prime256;
  (==) {lemma_exp_0 tD 1023 (pow2_10 + 1) (pow tD (2046 * pow2_19))}
  pow tD (1023 * (pow2_10 + 1)) * pow tD (2046 * pow2_19) % prime256;
  (==) {pow_plus tD (1023 * (pow2_10 + 1)) (2046 * pow2_19)}
  pow tD (1023 * (pow2_10 + 1) + 2046 * pow2_19) % prime256;
  }
  

val lemma_exp_3: tD: nat -> Lemma (pow (pow tD 2046 % prime256) (pow2 21) * pow (pow tD 1023 % prime256) (pow2 12 + 4) * pow (pow tD 3 % prime256) 1 % prime256 == pow tD (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) % prime256)

let lemma_exp_3 tD = 
  let pow2_21 = pow2 21 in 
  let pow2_12 = pow2 12 in 

  calc (==) {pow (pow tD 2046 % prime256) pow2_21 * pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1 % prime256;
  (==) {assert_by_tactic (pow (pow tD 2046 % prime256) pow2_21 * pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1 == pow (pow tD 2046 % prime256) pow2_21 * (pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1)) canon}
  pow (pow tD 2046 % prime256) pow2_21 * (pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1) % prime256;
  (==) {lemma_exp_0 tD 2046 pow2_21 (pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1)}
  pow tD (2046 * pow2_21) * (pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1) % prime256;
  (==) {assert_by_tactic (pow tD (2046 * pow2_21) * (pow (pow tD 1023 % prime256) (pow2_12 + 4) * pow (pow tD 3 % prime256) 1) == pow (pow tD 1023 % prime256) (pow2_12 + 4) * (pow tD (2046 * pow2_21) * pow (pow tD 3 % prime256) 1)) canon}
  pow (pow tD 1023 % prime256) (pow2_12 + 4) * (pow tD (2046 * pow2_21) * pow (pow tD 3 % prime256) 1) % prime256;
  (==) {lemma_exp_0 tD 1023 (pow2_12 + 4) (pow tD (2046 * pow2_21) * pow (pow tD 3 % prime256) 1)}
  pow tD (1023 * (pow2_12 + 4)) * (pow tD (2046 * pow2_21) * pow (pow tD 3 % prime256) 1) % prime256;
  (==) {assert_by_tactic (pow tD (1023 * (pow2_12 + 4)) * (pow tD (2046 * pow2_21) * pow (pow tD 3 % prime256) 1) == 
  pow (pow tD 3 % prime256) 1 * (pow tD (2046 * pow2_21) * pow tD (1023 * (pow2_12 + 4)))) canon}
  pow (pow tD 3 % prime256) 1 * (pow tD (2046 * pow2_21) * pow tD (1023 * (pow2_12 + 4))) % prime256;
  (==) {lemma_exp_0 tD 3 1 (pow tD (2046 * pow2_21) * pow tD (1023 * (pow2_12 + 4)))}
  pow tD 3 * (pow tD (2046 * pow2_21) * pow tD (1023 * (pow2_12 + 4))) % prime256;
  (==) {pow_plus tD (2046 * pow2_21) (1023 * (pow2_12 + 4))}
  pow tD 3 * pow tD (2046 * pow2_21 + 1023 * (pow2_12 + 4)) % prime256;
  (==) {pow_plus tD 3 (2046 * pow2_21 + 1023 * (pow2_12 + 4))}
  pow tD (3 + 2046 * pow2_21 + 1023 * (pow2_12 + 4)) % prime256;}
  

val lemma_exp_4: tD: nat -> Lemma (
  pow (pow tD (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) % prime256) (pow2 64) * 
      pow (pow tD (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) % prime256) (pow2 32) * 
      pow (pow tD (1023 * (pow2 10 + 1) + 2046 * pow2 19) % prime256) (pow2 2) * tD % prime256 ==
      pow tD (prime256 - 2) % prime256)
      
let lemma_exp_4 tD = 
  let pow2_128 = pow2 128 in 
  let pow2_64 = pow2 64 in 
  let pow2_32 = pow2 32 in 

    let a1 = (3 * (pow2 160 + 1) + 2046 * (pow2 181 + pow2 21) + 1023 * (pow2 172 + pow2 162 + pow2 12 + 4) + pow2 128) in 
  let a = pow (pow tD a1 % prime256) (pow2 64) in 
    let b1 = (3 + 2046 * pow2 21 + 1023 * (pow2 12 + 4)) in 
  let b = pow (pow tD b1 % prime256) (pow2 32) in 
    let c1 = (1023 * (pow2 10 + 1) + 2046 * pow2 19) in 
  let c =  pow (pow tD c1 % prime256) (pow2 2) * tD in 

  calc (==) { a * b * c  % prime256;
  (==) {assert_by_tactic (a * b * c == a * (b * c)) canon}
  a * (b * c) % prime256;
  (==) {lemma_exp_0 tD a1 pow2_64 (b * c)}
  pow tD (a1 * pow2_64) * (b * c) % prime256;
  (==) {assert_by_tactic (pow tD (a1 * pow2_64) * (b * c) == b * (pow tD (a1 * pow2_64) * c)) canon}
  b * (pow tD (a1 * pow2_64) * c) % prime256;  
  (==) {lemma_exp_0 tD b1 (pow2_32) (pow tD (a1 * pow2_64) * c)}
  pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * (pow (pow tD c1 % prime256) (pow2 2) * tD)) % prime256; 
  (==) {assert_by_tactic (pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * (pow (pow tD c1 % prime256) (pow2 2) * tD)) == 
    pow (pow tD c1 % prime256) (pow2 2) * (pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * tD))) canon}
  pow (pow tD c1 % prime256) (pow2 2) * (pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * tD)) % prime256;
  (==) {lemma_exp_0 tD c1 (pow2 2) (pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * tD))}
  pow tD (c1 * pow2 2) * (pow tD (b1 * pow2_32) * (pow tD (a1 * pow2_64) * pow tD 1)) % prime256;
  (==) {pow_plus tD (a1 * pow2_64) 1}
  pow tD (c1 * pow2 2) * (pow tD (b1 * pow2_32) * pow tD (a1 * pow2_64 + 1)) % prime256;
  (==) {pow_plus tD (b1 * pow2_32) (a1 * pow2_64 + 1)}
  pow tD (c1 * pow2 2) * pow tD (b1 * pow2_32 + a1 * pow2_64 + 1) % prime256;
  (==) {pow_plus tD (c1 * pow2 2) (b1 * pow2_32 + a1 * pow2_64 + 1)}
  pow tD (c1 * pow2 2 + b1 * pow2_32 + a1 * pow2_64 + 1) % prime256; };
  assert_norm (c1 * pow2 2 + b1 * pow2 32 + a1 * pow2 64 + 1 == prime256 - 2)

