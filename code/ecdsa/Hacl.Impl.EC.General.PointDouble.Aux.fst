module Hacl.Impl.EC.General.PointDouble.Aux

open Lib.IntTypes

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open FStar.Mul


val lemma_x3: #c: curve -> x: int -> y: int -> z: int -> Lemma (

  let alphaD = 3 * x * x + aCoordinate #c * (z * z) * (z * z) in 
  let prime = getPrime c in
  ((((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) - 8 * (x * (y * y))) % prime) == 
  ((alphaD * alphaD - 8 * (x * (y * y))) % prime))

let lemma_x3 #c x y z = 
  let prime = getPrime c in 
  let open FStar.Tactics.Canon in 
  let alphaD = 3 * x * x + aCoordinate #c * (z * z) * (z * z) in 

  calc (==) {
    ((((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) - 8 * (x * (y * y))) % prime);
    (==) {lemma_mod_add_distr (- 8 * (x * (y * y))) (((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime)) prime}
     ((((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) % prime - 8 * (x * (y * y))) % prime);
    (==) {lemma_mod_mul_distr_l (3 * x * x + aCoordinate #c * (z * z) * (z * z)) ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) prime}
    (((3 * x * x + aCoordinate #c * (z * z) * (z * z)) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime) % prime - 8 * (x * (y * y))) % prime);
    (==) {lemma_mod_mul_distr_r ((3 * x * x + aCoordinate #c * (z * z) * (z * z))) ((3 * x * x + aCoordinate #c * (z * z) * (z * z))) prime}
    (((3 * x * x + aCoordinate #c * (z * z) * (z * z)) * (3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime - 8 * (x * (y * y))) % prime);
    (==) {lemma_mod_add_distr (- 8 * (x * (y * y))) (((3 * x * x + aCoordinate #c * (z * z) * (z * z))) * ((3 * x * x + aCoordinate #c * (z * z) * (z * z)))) prime}
    ((alphaD * alphaD - 8 * (x * (y * y))) % prime);}

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0" 


val lemma_y3: #c: curve -> x: int -> y: int -> z: int -> x3: int -> Lemma (
  let prime = getPrime c in 
  let alphaD = 3 * x * x + aCoordinate #c * (z * z) * (z * z) in 
  let gammaD = y * y in 
  (alphaD % prime *  ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * (gammaD % prime) * (gammaD % prime)) % prime ==
  (alphaD *  (4 * (x * gammaD) - x3) - 8 * gammaD * gammaD) % prime)
  

let lemma_y3 #c x y z x3  = 
  let prime = getPrime c in 
  let alphaD = 3 * x * x + aCoordinate #c * (z * z) * (z * z) in 
  let gammaD = y * y in 


  calc (==) {alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) % prime;
    (==) {lemma_mod_mul_distr_l alphaD ((4 * (x * (gammaD % prime) % prime) % prime) - x3) prime}
    alphaD * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) % prime;    
    (==) {lemma_mod_mul_distr_r x gammaD prime}
    alphaD * ((4 * (x * gammaD % prime) % prime) - x3) % prime;   
    (==) {lemma_mod_mul_distr_r 4 (x * gammaD) prime}
    alphaD * ((4 * x * gammaD % prime) - x3) % prime;   
    (==) {lemma_mod_mul_distr_r alphaD ((4 * x * gammaD % prime) - x3) prime}
    alphaD * (((4 * x * gammaD % prime) - x3) % prime) % prime;   
    (==) {lemma_mod_add_distr (- x3) (4 * x * gammaD) prime}
    alphaD * ((4 * x * gammaD - x3) % prime) % prime;   
    (==) {lemma_mod_mul_distr_r alphaD (4 * x * gammaD - x3) prime}
    alphaD * (4 * x * gammaD - x3) % prime; };

  calc (==) {
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * (gammaD % prime) * (gammaD % prime)) % prime;
  (==) {}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * (gammaD % prime) * (gammaD % prime)) % prime;
  (==) {lemma_mod_sub_distr (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3)) (8 * (gammaD % prime) * (gammaD % prime)) prime}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * (gammaD % prime) * (gammaD % prime) % prime) % prime;
  (==) {lemma_mod_mul_distr_r (8 * (gammaD % prime)) gammaD prime}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * (gammaD % prime) * (gammaD) % prime) % prime;
  (==) {assert_by_tactic (8 * (gammaD % prime) * (gammaD) == 8 * gammaD * (gammaD % prime)) canon}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * gammaD * (gammaD % prime) % prime) % prime;
  (==) {lemma_mod_mul_distr_r (8 * gammaD) gammaD prime}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * gammaD * gammaD % prime) % prime;
  (==) {lemma_mod_sub_distr (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3)) (8 * (gammaD) * (gammaD)) prime}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) - 8 * gammaD * gammaD) % prime;
  (==) {lemma_mod_add_distr (- 8 * gammaD * gammaD) (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3)) prime}
    (alphaD % prime * ((4 * (x * (gammaD % prime) % prime) % prime) - x3) % prime - 8 * gammaD * gammaD) % prime;
  (==) {}
    (alphaD * (4 * x * gammaD - x3) % prime - 8 * gammaD * gammaD) % prime;
  (==) {lemma_mod_add_distr (- 8 * gammaD * gammaD) (alphaD * (4 * x * gammaD - x3)) prime}
    (alphaD * (4 * x * gammaD - x3) - 8 * gammaD * gammaD) % prime;
  (==) {assert_by_tactic (4 * x * gammaD == 4 * (x * gammaD)) canon}
    (alphaD * (4 * (x * gammaD) - x3) - 8 * gammaD * gammaD) % prime;}

val lemma_z3: #c: curve ->  x: int -> y: int -> z: int -> Lemma (
  let prime = getPrime c in 
  ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime 
  == ((y + z) * (y + z) - z * z - y * y) % prime)


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

