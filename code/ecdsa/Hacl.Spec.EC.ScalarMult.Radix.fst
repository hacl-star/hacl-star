module Hacl.Spec.EC.ScalarMult.Radix

open FStar.Math.Lemmas
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Impl.EC.Math

open FStar.Mul



#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0 "

(* the same in Hacl.Impl.EC.Math --- *)
assume val lemma_exp_not_zero: p: nat {Math.Euclid.is_prime p} -> a: nat {a % p <> 0} -> k: pos ->
  Lemma (Spec.ECC.Curves.exp #p (a % p) k % p <> 0)

assume val lemma_a_not_zero_b_not_zero_mod_not_zero: p: nat {Math.Euclid.is_prime p} -> a: nat {a % p <> 0} -> b: nat {b % p <> 0} ->
  Lemma (requires a * b <> 0)
  (ensures a * b % p <> 0)


val lemma_point_add_mixed_b_is_infinity_x_after_norm: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ isPointAtInfinity #Affine b /\ not (isPointAtInfinity #Jacobian a)} 
  -> Lemma (let aX, aY, aZ = a in aX * exp #(getPrime c) (aZ * aZ % getPrime c) (getPrime c - 2) % (getPrime c) == 0)

let lemma_point_add_mixed_b_is_infinity_x_after_norm #c a b = 
  let aX, aY, aZ = a in
  let prime = getPrime c in  
  assert(0 == aX * exp #prime (aZ * aZ % prime) (prime - 2) % prime)  

val lemma_point_add_mixed_b_is_infinity_y_after_norm: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ isPointAtInfinity #Affine b /\ not (isPointAtInfinity #Jacobian a)} 
  -> Lemma (let aX, aY, aZ = a in aY * exp #(getPrime c) (aZ * aZ * aZ % getPrime c) (getPrime c - 2) % (getPrime c) == 0)

let lemma_point_add_mixed_b_is_infinity_y_after_norm #c a b = 
  let aX, aY, aZ = a in
  let prime = getPrime c in  
  assert(0 == aY * exp #prime (aZ * aZ * aZ % prime) (prime - 2) % prime)  


val lemma_point_add_mixed_b_is_infinity_0: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ isPointAtInfinity #Affine b /\ not (isPointAtInfinity #Jacobian a)} 
  -> d: point_nat_prime #c
  -> Lemma (let aX,  aY, aZ = a in aX == 0)

let lemma_point_add_mixed_b_is_infinity_0 #c a b d = 
  let open FStar.Math.Euclid in 
  let aX, aY, aZ = a in
  let prime = getPrime c in   
  let pAffineX, pAffineY, pAffineZ = _norm a in 
  
  let open FStar.Math.Lemmas in 
  pos_times_pos_is_pos aZ aZ;
  lemma_a_not_zero_b_not_zero_mod_not_zero prime aZ aZ; 
  lemma_exp_not_zero prime (aZ * aZ) (prime - 2); 
  lemma_point_add_mixed_b_is_infinity_x_after_norm #c a b;
  FStar.Math.Euclid.euclid_prime prime aX (exp #prime (aZ * aZ % prime) (prime - 2));
  FStar.Math.Lemmas.small_mod aX prime


val lemma_point_add_mixed_b_is_infinity_1: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ isPointAtInfinity #Affine b /\ not (isPointAtInfinity #Jacobian a)} 
  -> d: point_nat_prime #c
  -> Lemma (let aX, aY, aZ = a in aY == 0)

let lemma_point_add_mixed_b_is_infinity_1 #c a b d = 
  let aX, aY, aZ = a in
  let prime = getPrime c in 
  let pAffineX, pAffineY, pAffineZ = _norm a in 

  let open FStar.Math.Lemmas in 
  pos_times_pos_is_pos (aZ) aZ;
  pos_times_pos_is_pos (aZ * aZ) aZ;

  lemma_a_not_zero_b_not_zero_mod_not_zero prime (aZ) aZ; 
  lemma_a_not_zero_b_not_zero_mod_not_zero prime (aZ * aZ) aZ; 
  lemma_exp_not_zero prime (aZ * aZ * aZ) (prime - 2);
  lemma_point_add_mixed_b_is_infinity_y_after_norm #c a b;

  FStar.Math.Euclid.euclid_prime prime aY (exp #prime (aZ * aZ * aZ % prime) (prime - 2));
  FStar.Math.Lemmas.small_mod aY prime


val lemma_point_add_mixed_b_is_infinity: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ isPointAtInfinity #Affine b /\ not (isPointAtInfinity #Jacobian a)} 
  -> d: point_nat_prime #c -> Lemma (pointEqual (_point_add_mixed #c d a) (_point_add_mixed d b))

let lemma_point_add_mixed_b_is_infinity #c a b d =
  lemma_point_add_mixed_b_is_infinity_0 a b d; lemma_point_add_mixed_b_is_infinity_1 a b d


val lemma_point_add_mixed_two_points: #c: curve 
  -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ not (isPointAtInfinity #Affine a) /\ not (isPointAtInfinity #Jacobian b)} 
  -> d: point_nat_prime #c {not (isPointAtInfinity #Affine b) /\ not (pointEqual d b)} -> Lemma (
     pointEqual (_point_add_mixed d b) (_point_add_mixed d a))

let lemma_point_add_mixed_two_points #c a b d = 
  assert(_point_add_mixed d b == pointAdd d b);
  assert(_point_add_mixed d a == pointAdd d a);

  curve_compatibility_with_translation_lemma a b d;
  assert(pointEqual (pointAdd b d) (pointAdd a d));

  curve_commutativity_lemma b d; 
  curve_commutativity_lemma a d


#push-options "--z3rlimit 500"

val lemma_not_affine_equality: #c: curve -> a: point_nat_prime #c
  -> b: point_nat_prime #c {pointEqual a b /\ not (isPointAtInfinity #Affine b) /\ not (isPointAtInfinity #Jacobian b)} 
  -> Lemma (not (isPointAtInfinity #Affine a))

let lemma_not_affine_equality #c a b =
  let prime = getPrime c in 
  let aX, aY, aZ = a in 
  let bX, bY, bZ = b in 

  assert(bX < prime /\ bY < prime);
  small_mod bX prime;
  small_mod bY prime;

  pos_times_pos_is_pos bZ bZ;
  pos_times_pos_is_pos (bZ * bZ) bZ;
  lemma_a_not_zero_b_not_zero_mod_not_zero prime bZ bZ; 
  lemma_a_not_zero_b_not_zero_mod_not_zero prime (bZ * bZ) bZ; 

  assert(Math.Euclid.is_prime prime);
  lemma_exp_not_zero prime (bZ * bZ) (prime - 2); 
  lemma_exp_not_zero prime (bZ * bZ * bZ) (prime - 2); 
  
  if bX <> 0 then 
    begin
    FStar.Math.Lemmas.pos_times_pos_is_pos bX (exp #prime (bZ * bZ % prime) (prime - 2));
    lemma_a_not_zero_b_not_zero_mod_not_zero prime bX (exp #prime (bZ * bZ % prime) (prime - 2))
    end;

  if bY <> 0 then  begin
    FStar.Math.Lemmas.pos_times_pos_is_pos bY (exp #prime (bZ * bZ * bZ % prime) (prime - 2));
    lemma_a_not_zero_b_not_zero_mod_not_zero prime bY (exp #prime (bZ * bZ * bZ % prime) (prime - 2))
    end;

  assert(not (isPointAtInfinity #Affine a))
