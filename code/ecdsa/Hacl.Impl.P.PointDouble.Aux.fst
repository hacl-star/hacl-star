module Hacl.Impl.P.PointDouble.Aux

open Lib.IntTypes

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open FStar.Mul


val lemma_x3_0: #c: curve -> x: int -> y: int -> z: int -> 
  Lemma (
    let prime = getPrime c in 
    let zzprime = z * z % prime in 
    ((3 * (x - zzprime) * (x + zzprime) % prime) * (3 * (x - zzprime) * (x + zzprime) % prime) - 8 * (x * (y * y % prime) % prime)) % prime == 
    ((3 * (x - zzprime) * (x + zzprime) % prime) * (3 * (x - zzprime) * (x + zzprime) % prime) - 8 * x * y * y) % prime)

let lemma_x3_0 #c x y z = 
  let prime = getPrime c in
  let open FStar.Tactics.Canon in 
  let t0 = (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) in 
  calc (==)
  {
    (t0 * t0 - 8 * (x * (y * y % prime) % prime)) % prime;
    
    (==) {lemma_mod_mul_distr_r x (y * y) prime}
    
    (t0 * t0 - 8 * ((x * (y * y)) % prime)) % prime;
    
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
    
    (t0 * t0 - 8 * (x * y * y % prime)) % prime;
    
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * (x * y * y % prime)) prime}
    
    (t0 * t0 - (8 * (x * y * y % prime)) % prime) % prime;
    
    (==) {lemma_mod_mul_distr_r 8 (x * y * y) prime}
    
    (t0 * t0 - (8 * (x * y * y)) % prime) % prime;
    
    (==) {assert_by_tactic (8 * (x * y * y) == 8 * x * y * y) canon}
    
    (t0 * t0 - (8 * x * y * y) % prime) % prime;
    
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * x * y * y) prime}
    
    (t0 * t0 - 8 * x * y * y) % prime;
  }


val lemma_x3_1: #c : curve -> a: int -> b: int -> Lemma 
  ( 
    let prime = getPrime c in 
    ((a % prime) * (a % prime) - b) % prime == (a * a - b) % prime
  )

let lemma_x3_1 #c a b = 
  let prime = getPrime c in 
  calc (==)
  {
    ((a % prime) * (a % prime) - b) % prime;
    
    (==) {lemma_mod_add_distr (- b) ((a % prime) * (a % prime)) prime}
    
    ((a % prime) * (a % prime) % prime - b) % prime;
    
    (==) {lemma_mod_mul_distr_l a (a % prime) prime; lemma_mod_mul_distr_r a a prime}
    
    (a * a % prime - b) % prime;
    
    (==) {lemma_mod_add_distr (- b) (a * a) prime}
    
    (a * a - b) % prime;
  }
  

val lemma_x3: #c: curve -> x: int -> y: int -> z: int -> Lemma (
  let prime = getPrime c in 
  let zzprime = z * z % prime in 
  ((3 * (x - zzprime) * (x + zzprime) % prime) * (3 * (x - zzprime) * (x + zzprime) % prime)  - 8 * (x * (y * y % prime) % prime)) % prime == 
  ((3 * (x - z * z) * (x + z * z)) * (3 * (x - z * z) * (x + z * z)) - 8 * x * (y * y)) % prime
)

let lemma_x3 #c x y z = 
  let prime = getPrime c in 
  let open FStar.Tactics.Canon in 
  lemma_x3_0 #c x y z;

  calc (==)
  {
    ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
    
    (==) {lemma_mod_mul_distr_l (3 * (x - (z * z % prime))) (x + (z * z % prime)) prime}
    
    ((3 * (x - (z * z % prime)) % prime * (x + (z * z % prime)) % prime) * (3 * (x - (z * z % prime)) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
    
    (==) {lemma_mod_mul_distr_r 3 (x - (z * z % prime)) prime}
  
    ((3 * ((x - (z * z % prime)) % prime) % prime * (x + (z * z % prime)) % prime) * (3 * ((x - (z * z % prime)) % prime) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

    (==) {lemma_mod_sub_distr x (z * z) prime}

    ((3 * ((x - z * z) % prime) % prime * (x + (z * z % prime)) % prime) * (3 * ((x - z * z) % prime) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

    (==) {lemma_mod_mul_distr_r 3 (x - (z * z)) prime}
  
    ((3 * ((x - z * z)) % prime * (x + (z * z % prime)) % prime) * (3 * ((x - z * z)) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

    (==) {lemma_mod_mul_distr_l (3 * (x - z * z)) (x + (z * z % prime)) prime}

    ((3 * (x - z * z) * (x + (z * z % prime)) % prime) * (3 * (x - z * z) * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
     
    (==) {lemma_mod_mul_distr_r (3 * (x - z * z)) (x + (z * z % prime)) prime; lemma_mod_add_distr x (z * z) prime; lemma_mod_mul_distr_r (3 * (x - z * z)) (x + z * z) prime}

    ((3 * (x - z * z) * (x + (z * z)) % prime) * (3 * (x - z * z) * (x + (z * z)) % prime) - 8 * x * y * y) % prime;
  
    (==) {lemma_x3_1 #c (3 * (x - z * z) * (x + (z * z))) (8 * x * y * y)}

    ((3 * (x - z * z) * (x + z * z)) * (3 * (x - z * z) * (x + z * z)) - 8 * x * y * y) % prime;

    (==) {assert_by_tactic (8 * x * y * y == 8 * x * (y * y)) canon}
     
    ((3 * (x - z * z) * (x + z * z)) * (3 * (x - z * z) * (x + z * z)) - 8 * x * (y * y)) % prime;
  }


val y3_lemma_0: #c: curve -> x: int ->  y: int -> z: int -> t0: int -> Lemma (
  let prime = getPrime c in 
  (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime == (t0 - 8 * y * y * y * y) % prime)

let y3_lemma_0 #c x y z t0 = 
  let prime = getPrime c in 
  calc (==) {
    (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime;
  (==) {lemma_mod_sub_distr t0 (8 * (y * y % prime) * (y * y % prime)) prime}
    (t0 - (8 * (y * y % prime) * (y * y % prime)) % prime) % prime;  
  (==) {lemma_mod_mul_distr_r (8 * (y * y % prime)) (y * y) prime}
    (t0 - (8 * (y * y % prime) * (y * y)) % prime) % prime;
  (==) {assert_by_tactic (8 * (y * y) * (y * y % prime) == 8 * (y * y % prime) * (y * y)) canon}
    (t0 - (8 * (y * y) * (y * y  % prime)) % prime) % prime;
  (==) {lemma_mod_mul_distr_r (8 * (y * y)) (y * y) prime}
    (t0 - (8 * (y * y) * (y * y)) % prime) % prime; 
  (==) {assert_by_tactic (8 * (y * y) * (y * y) == 8 * y * y * y * y) canon}
    (t0 - (8 * y * y * y * y) % prime) % prime;
  (==) {lemma_mod_sub_distr t0 (8 * y * y * y * y) prime}
    (t0 - (8 * y * y * y * y)) % prime;
  (==) {assert_by_tactic (t0 - (8 * y * y * y * y) == t0 - 8 * y * y * y * y) canon}
    (t0 - 8 * y * y * y * y) % prime;}


val y3_lemma_1: #c: curve -> x: int ->  y: int -> z: int -> Lemma (
  let prime = getPrime c in 
  3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime == 
  3 * (x + z * z) * (x - z * z)  % prime)

let y3_lemma_1 #c x y z = 
  let prime = getPrime c in 
  let open FStar.Tactics.Canon in 
  calc (==)
  {
    3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % prime))) (x + (z * z % prime)) prime}
      3 * (x - (z * z % prime)) * ((x + (z * z % prime)) % prime) % prime; 
    (==) {lemma_mod_add_distr x (z * z) prime}
      3 * (x - (z * z % prime)) * ((x + z * z) % prime) % prime; 
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % prime))) (x + z * z) prime}
      3 * (x - (z * z % prime)) * (x + z * z) % prime; 
    (==) {assert_by_tactic (3 * (x - (z * z % prime)) * (x + z * z) == 3 * (x + z * z) * (x - (z * z % prime))) canon}
      3 * (x + z * z) * (x - (z * z % prime)) % prime; 
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z)) (x - (z * z % prime)) prime}
      3 * (x + z * z) * ((x - (z * z % prime))  % prime) % prime; 
    (==) {lemma_mod_sub_distr x (z * z) prime}
      3 * (x + z * z) * ((x - z * z) % prime) % prime; 
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z)) (x - z * z) prime}
      3 * (x + z * z) * ((x - z * z)) % prime; 
    (==) {assert_by_tactic (3 * (x + z * z) * (x - z * z) == 3 * (x - z * z) * (x + z * z)) canon}
      3 * (x + z * z) * (x - z * z)  % prime; 
    }


val lemma_y3: #c: curve -> x: int -> y: int -> z: int -> x3: int -> Lemma (
  let prime = getPrime c in 
  let zzprime = z * z % prime in
  ((3 * (x - zzprime) * (x + zzprime) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) - 8 * (y * y % prime) * (y * y % prime)) % prime == 
  (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % prime)
  

let lemma_y3 #c x y z x3 = 
  let prime = getPrime c in 
  let open FStar.Tactics.Canon in 
  let t = ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) - 8 * (y * y % prime) * (y * y % prime)) % prime in 
  let t0 = (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) in 
  assert(t == (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime);

  y3_lemma_0 #c x y z t0;
  y3_lemma_1 #c x y z;


  calc (==)
  {
      4 * (x * (y * y % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r x (y * y) prime}
       4 * ((x * (y * y)) % prime) % prime;
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
      (4 * ((x * y * y) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r 4 (x * y * y) prime}
      (4 * (x * y * y)) % prime;
    (==) {assert_by_tactic (4 * (x * y * y) == 4 * x * y * y) canon}
      4 * x * y * y % prime;
      
   };

  calc (==)
  {
    ((3 * (x + z * z) * (x - z * z)  % prime) *  (4 * x * y * y % prime - x3) - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) ((3 * (x + z * z) * (x - z * z)  % prime) *  (4 * x * y * y % prime - x3)) prime}
    ((((3 * (x + z * z) * (x - z * z)) % prime) *  (4 * x * y * y % prime - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_l (3 * (x + z * z) * (x - z * z))  (4 * x * y * y % prime - x3) prime}
    (((3 * (x + z * z) * (x - z * z)) *  (4 * x * y * y % prime - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y % prime - x3) prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y % prime - x3) % prime)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- x3) (4 * x * y * y) prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y - x3) % prime)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y - x3) prime}
    ((3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) prime}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * y * y * y * y) % prime;
    (==) {assert_by_tactic (8 * y * y * y * y == 8 * (y * y) * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * (y * y) * (y * y)) % prime;
    (==) {assert_by_tactic (4 * x * y * y == 4 * x * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % prime;
    (==) {assert_by_tactic ((3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) == (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y))) canon}
    (3 * (x - z * z) * (x + z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % prime;
  }
 

val lemma_z3: #c: curve ->  x: int -> y: int -> z: int -> Lemma (
  let prime = getPrime c in 
  ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime == ((y + z) * (y + z) - z * z - y * y) % prime)


let lemma_z3 #c x y z = 
  let prime = getPrime c in 
  let t = ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime in 
  calc (==) 
    {
      ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - (y * y % prime)) (z * z) prime}
      ((y + z) * (y + z) - (y * y % prime) - z * z) % prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - z * z) (y * y) prime}
      ((y + z) * (y + z) - z * z - y * y) % prime;
    }


val lemma_point_abd: xD: int -> dlt: int -> 
  Lemma (3 * (xD - dlt) * (xD + dlt) == 3 * ((xD - dlt) * (xD + dlt)))

let lemma_point_abd xD dlt = ()

