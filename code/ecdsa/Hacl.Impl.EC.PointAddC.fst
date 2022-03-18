module Hacl.Impl.EC.PointAddC

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC

open FStar.Math.Lemmas
open Hacl.Impl.EC.Masking
open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.NIST.PointDouble
open Hacl.Impl.EC.PointAdd

open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul
open FStar.Math.Lib


open FStar.Tactics 
open FStar.Tactics.Canon 

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val lemma_multiplication_is_pointEqual_l0: #c: curve 
  -> p: point_nat_prime #c {let pX, pY, pZ = p in pZ * pZ % getPrime c <> 0}
  -> q: point_nat_prime #c {let qX, qY, qZ = q in qZ * qZ % getPrime c <> 0} -> 
  Lemma (
    let pX, pY, pZ = p in 
    let qX, qY, qZ = q in 
    let prime = getPrime c in 
    pX * (qZ * qZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime == pX * modp_inv2 #c (pZ * pZ) % prime /\ 
    qX * (pZ * pZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime == qX * modp_inv2 #c (qZ * qZ)  % prime)


let lemma_multiplication_is_pointEqual_l0 #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 

  calc (==) {pX * (qZ * qZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (pX * (qZ * qZ)) (modp_inv2 #c (pZ * pZ)) prime}
  pX * (qZ * qZ) * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (pX * (qZ * qZ) * modp_inv2 #c (pZ * pZ)) (modp_inv2 #c (qZ * qZ)) prime}
  pX * (qZ * qZ) * modp_inv2 #c (pZ * pZ) * modp_inv2 #c (qZ * qZ) % prime;	
    (==) {assert_by_tactic (pX * (qZ * qZ) * modp_inv2 #c (pZ * pZ) * modp_inv2 #c (qZ * qZ) == pX * modp_inv2 #c (pZ * pZ) * ((qZ * qZ) * modp_inv2 #c (qZ * qZ))) canon}
  pX * modp_inv2 #c (pZ * pZ) * ((qZ * qZ) * modp_inv2 #c (qZ * qZ)) % prime;
    (==) {lemma_mod_mul_distr_r (pX * modp_inv2 #c (pZ * pZ)) ((qZ * qZ) * modp_inv2 #c (qZ * qZ)) prime}
  pX * modp_inv2 #c (pZ * pZ) * ((qZ * qZ) * modp_inv2 #c (qZ * qZ) % prime) % prime; 
    (==) {lemma_mod_inv2_mult_prime prime (qZ * qZ)}
  pX * modp_inv2 #c (pZ * pZ)  % prime;};

  calc (==) {qX * (pZ * pZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (qX * (pZ * pZ)) (modp_inv2 #c (pZ * pZ)) prime}
  qX * (pZ * pZ) * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (qX * (pZ * pZ) * modp_inv2 #c (pZ * pZ)) (modp_inv2 #c (qZ * qZ)) prime}
  qX * (pZ * pZ) * modp_inv2 #c (pZ * pZ) * modp_inv2 #c (qZ * qZ) % prime;
    (==) {assert_by_tactic (qX * (pZ * pZ) * modp_inv2 #c (pZ * pZ) * modp_inv2 #c (qZ * qZ) == qX * modp_inv2 #c (qZ * qZ) * ((pZ * pZ) * modp_inv2 #c (pZ * pZ))) canon}
  qX * modp_inv2 #c (qZ * qZ) * ((pZ * pZ) * modp_inv2 #c (pZ * pZ)) % prime; 
    (==) {lemma_mod_mul_distr_r (qX * modp_inv2 #c (qZ * qZ)) ((pZ * pZ) * modp_inv2 #c (pZ * pZ)) prime}
  qX * modp_inv2 #c (qZ * qZ) * ((pZ * pZ) * modp_inv2 #c (pZ * pZ) % prime) % prime; 
    (==) {lemma_mod_inv2_mult_prime prime (pZ * pZ)}
  qX * modp_inv2 #c (qZ * qZ)  % prime; }


val lemma_multiplication_is_pointEqual_l1: #c: curve 
  -> p: point_nat_prime #c {let pX, pY, pZ = p in pZ * pZ * pZ % getPrime c <> 0}
  -> q: point_nat_prime #c {let qX, qY, qZ = q in qZ * qZ * qZ % getPrime c <> 0} -> 
  Lemma (
    let pX, pY, pZ = p in 
    let qX, qY, qZ = q in 
    let prime = getPrime c in 
    pY * (qZ * qZ * qZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime == pY * modp_inv2 #c (pZ * pZ * pZ) % prime /\ 
    qY * (pZ * pZ * pZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime == qY * modp_inv2 #c (qZ * qZ * qZ) % prime)


let lemma_multiplication_is_pointEqual_l1 #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  
  calc (==) {pY * (qZ * qZ * qZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime;
	 (==) {lemma_mod_mul_distr_l (pY * (qZ * qZ * qZ)) (modp_inv2 #c (pZ * pZ * pZ)) prime}
      pY * (qZ * qZ * qZ) * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime;
	(==) {lemma_mod_mul_distr_l (pY * (qZ * qZ * qZ) * modp_inv2 #c (pZ * pZ * pZ)) (modp_inv2 #c (qZ * qZ * qZ)) prime}
      pY * (qZ * qZ * qZ) * modp_inv2 #c (pZ * pZ * pZ) * modp_inv2 #c (qZ * qZ * qZ) % prime;	
	(==) {assert_by_tactic (pY * (qZ * qZ * qZ) * modp_inv2 #c (pZ * pZ * pZ) * modp_inv2 #c (qZ * qZ * qZ) == pY * modp_inv2 #c (pZ * pZ * pZ) * ((qZ * qZ * qZ) * modp_inv2 #c (qZ * qZ * qZ))) canon}
      pY * modp_inv2 #c (pZ * pZ * pZ) * ((qZ * qZ * qZ) * modp_inv2 #c (qZ * qZ * qZ)) % prime;
	(==) {lemma_mod_mul_distr_r (pY * modp_inv2 #c (pZ * pZ * pZ)) ((qZ * qZ * qZ) * modp_inv2 #c (qZ * qZ * qZ)) prime}
      pY * modp_inv2 #c (pZ * pZ * pZ) * ((qZ * qZ * qZ) * modp_inv2 #c (qZ * qZ * qZ) % prime) % prime; 
	(==) {lemma_mod_inv2_mult_prime prime (qZ * qZ * qZ)}
      pY * modp_inv2 #c (pZ * pZ * pZ) % prime;}; 

      calc (==) {qY * (pZ * pZ * pZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime;
	 (==) {lemma_mod_mul_distr_l (qY * (pZ * pZ * pZ)) (modp_inv2 #c (pZ * pZ * pZ)) prime}
      qY * (pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime;
	(==) {lemma_mod_mul_distr_l (qY * (pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ)) (modp_inv2 #c (qZ * qZ * qZ)) prime}
      qY * (pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ) * modp_inv2 #c (qZ * qZ * qZ) % prime;
	(==) {assert_by_tactic (qY * (pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ) * modp_inv2 #c (qZ * qZ * qZ) == qY * modp_inv2 #c (qZ * qZ * qZ) * ((pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ))) canon}
      qY * modp_inv2 #c (qZ * qZ * qZ) * ((pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ)) % prime; 
	(==) {lemma_mod_mul_distr_r (qY * modp_inv2 #c (qZ * qZ * qZ)) ((pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ)) prime}
      qY * modp_inv2 #c (qZ * qZ * qZ) * ((pZ * pZ * pZ) * modp_inv2 #c (pZ * pZ * pZ) % prime) % prime; 
	(==) {lemma_mod_inv2_mult_prime prime (pZ * pZ * pZ)}
      qY * modp_inv2 #c (qZ * qZ * qZ) % prime; }



(* val lemma_multiplication_is_pointEqual_l: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} 
  -> q: point_nat_prime #c {~ (isPointAtInfinity q)} -> 
  Lemma (
    let pX, pY, pZ = p in
    let qX, qY, qZ = q in 
    ((pX * (qZ * qZ) % getPrime c == qX * (pZ * pZ) % getPrime c) /\
    (pY * (qZ * qZ * qZ) % getPrime c == qY * (pZ * pZ * pZ) % getPrime c)) ==> pointEqual p q)


let lemma_multiplication_is_pointEqual_l #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  
  let pNX, pNY, pNZ = _norm p in 
  let qNX, qNY, qNZ = _norm q in 

  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime qZ qZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime pZ pZ;
  
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (pZ * pZ) pZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (qZ * qZ) qZ;

  
  if pX * (qZ * qZ) % prime = qX * (pZ * pZ) % prime then begin
    assert(pX * (qZ * qZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime = qX * (pZ * pZ) % prime * modp_inv2 #c (pZ * pZ) % prime * modp_inv2 #c (qZ * qZ) % prime);
    lemma_multiplication_is_pointEqual_l0 p q end;

  if pY * (qZ * qZ * qZ) % prime = qY * (pZ * pZ * pZ) % prime then begin
    assert(pY * (qZ * qZ * qZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime = qY * (pZ * pZ * pZ) % prime * modp_inv2 #c (pZ * pZ * pZ) % prime * modp_inv2 #c (qZ * qZ * qZ) % prime);
    lemma_multiplication_is_pointEqual_l1 p q 
  end

 *)
 
val lemma_multiplication_is_pointEqual_r0: #c: curve 
  -> p: point_nat_prime #c {let pX, pY, pZ = p in pZ * pZ % getPrime c <> 0}
  -> q: point_nat_prime #c {let qX, qY, qZ = q in qZ * qZ % getPrime c <> 0} -> 
  Lemma (
    let pX, pY, pZ = p in 
    let qX, qY, qZ = q in 
    let prime = getPrime c in 
    pX * modp_inv2 #c (pZ * pZ) % prime * (pZ * pZ) * (qZ * qZ) % prime == pX * (qZ * qZ) % prime /\
    qX * modp_inv2 #c (qZ * qZ) % prime * (pZ * pZ) * (qZ * qZ) % prime == qX * (pZ * pZ) % prime)

let lemma_multiplication_is_pointEqual_r0 #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 

  calc (==) {pX * modp_inv2 #c (pZ * pZ) % prime * (pZ * pZ) * (qZ * qZ) % prime;
    (==) {lemma_mod_mul_distr_l (pX * modp_inv2 #c (pZ * pZ)) ((pZ * pZ) * (qZ * qZ)) prime}
  pX * modp_inv2 #c (pZ * pZ) * ((pZ * pZ) * (qZ * qZ)) % prime;
    (==) {assert_by_tactic (pX * modp_inv2 #c (pZ * pZ) * ((pZ * pZ) * (qZ * qZ)) == 
      pX * (qZ * qZ) * (modp_inv2 #c (pZ * pZ) * (pZ * pZ))) canon}
  pX * (qZ * qZ) * (modp_inv2 #c (pZ * pZ) * (pZ * pZ)) % prime; 
    (==) {lemma_mod_mul_distr_r (pX * (qZ * qZ)) (modp_inv2 #c (pZ * pZ) * (pZ * pZ)) prime}
  pX * (qZ * qZ) * (modp_inv2 #c (pZ * pZ) * (pZ * pZ) % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime (pZ * pZ)}
  pX * (qZ * qZ) % prime;};


  calc (==) {qX * modp_inv2 #c (qZ * qZ) % prime * (pZ * pZ) * (qZ * qZ) % prime;
    (==) {assert_by_tactic (qX * modp_inv2 #c (qZ * qZ) % prime * (pZ * pZ) * (qZ * qZ) == 
    qX * modp_inv2 #c (qZ * qZ) % prime * ((pZ * pZ) * (qZ * qZ))) canon}
  qX * modp_inv2 #c (qZ * qZ) % prime * ((pZ * pZ) * (qZ * qZ)) % prime;
    (==) {lemma_mod_mul_distr_l (qX * modp_inv2 #c (qZ * qZ)) ((pZ * pZ) * (qZ * qZ)) prime}
  qX * modp_inv2 #c (qZ * qZ) * ((pZ * pZ) * (qZ * qZ)) % prime; 
    (==) {assert_by_tactic (qX * modp_inv2 #c (qZ * qZ) * ((pZ * pZ) * (qZ * qZ)) == 
      qX * (pZ * pZ) * (modp_inv2 #c (qZ * qZ) * (qZ * qZ))) canon}
  qX * (pZ * pZ) * (modp_inv2 #c (qZ * qZ) * (qZ * qZ)) % prime; 
    (==) {lemma_mod_mul_distr_r (qX * (pZ * pZ)) (modp_inv2 #c (qZ * qZ) * (qZ * qZ)) prime}
  qX * (pZ * pZ) * (modp_inv2 #c (qZ * qZ) * (qZ * qZ) % prime) % prime;
    (==) {lemma_mod_inv2_mult_prime prime (qZ * qZ)}
  qX * (pZ * pZ) % prime; }



val lemma_multiplication_is_pointEqual_r1: #c: curve 
  -> p: point_nat_prime #c {let pX, pY, pZ = p in pZ * pZ * pZ % getPrime c <> 0}
  -> q: point_nat_prime #c {let qX, qY, qZ = q in qZ * qZ * qZ % getPrime c <> 0} -> 
  Lemma (
    let pX, pY, pZ = p in 
    let qX, qY, qZ = q in 
    let prime = getPrime c in 
    pY * modp_inv2 #c (pZ * pZ * pZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime == pY * (qZ * qZ * qZ) % prime /\
    qY * modp_inv2 #c (qZ * qZ * qZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime == qY * (pZ * pZ * pZ) % prime)

let lemma_multiplication_is_pointEqual_r1 #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 

    calc (==) {pY * modp_inv2 #c (pZ * pZ * pZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime;
      (==) {assert_by_tactic (pY * modp_inv2 #c (pZ * pZ * pZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) == 
      pY * modp_inv2 #c (pZ * pZ * pZ) % prime * ((pZ * pZ * pZ) * (qZ * qZ * qZ))) canon}
    pY * modp_inv2 #c (pZ * pZ * pZ) % prime * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) % prime;
      (==) {lemma_mod_mul_distr_l (pY * modp_inv2 #c (pZ * pZ * pZ)) ((pZ * pZ * pZ) * (qZ * qZ * qZ)) prime}
    pY * modp_inv2 #c (pZ * pZ * pZ) * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) % prime; 
      (==) {assert_by_tactic (pY * modp_inv2 #c (pZ * pZ * pZ) * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) == 
	pY * (qZ * qZ * qZ) * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ))) canon}
    pY * (qZ * qZ * qZ) * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ)) % prime; 
     (==) {lemma_mod_mul_distr_r (pY * (qZ * qZ * qZ)) (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ)) prime}
    pY * (qZ * qZ * qZ) * (modp_inv2 #c (pZ * pZ * pZ) * (pZ * pZ * pZ) % prime) % prime;
      (==) {lemma_mod_inv2_mult_prime prime (pZ * pZ * pZ)}
    pY * (qZ * qZ * qZ) % prime;};

    calc (==) {qY * modp_inv2 #c (qZ * qZ * qZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime;
      (==) {assert_by_tactic (qY * modp_inv2 #c (qZ * qZ * qZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) == 
      qY * modp_inv2 #c (qZ * qZ * qZ) % prime * ((pZ * pZ * pZ) * (qZ * qZ * qZ))) canon}
    qY * modp_inv2 #c (qZ * qZ * qZ) % prime * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) % prime;
      (==) {lemma_mod_mul_distr_l (qY * modp_inv2 #c (qZ * qZ * qZ)) ((pZ * pZ * pZ) * (qZ * qZ * qZ)) prime}
    qY * modp_inv2 #c (qZ * qZ * qZ) * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) % prime;
      (==) {assert_by_tactic (qY * modp_inv2 #c (qZ * qZ * qZ) * ((pZ * pZ * pZ) * (qZ * qZ * qZ)) == 
	qY * (pZ * pZ * pZ) * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ))) canon}
    qY * (pZ * pZ * pZ) * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ)) % prime; 
      (==) {lemma_mod_mul_distr_r (qY * (pZ * pZ * pZ)) (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ)) prime}
    qY * (pZ * pZ * pZ) * (modp_inv2 #c (qZ * qZ * qZ) * (qZ * qZ * qZ) % prime) % prime;
      (==) {lemma_mod_inv2_mult_prime prime (qZ * qZ * qZ)}
    qY * (pZ * pZ * pZ) % prime;}


(* val lemma_multiplication_is_pointEqual_r: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} 
  -> q: point_nat_prime #c {~ (isPointAtInfinity q)} -> 
  Lemma (
    let pX, pY, pZ = p in
    let qX, qY, qZ = q in 
    _norm p == _norm q ==> ((pX * (qZ * qZ) % getPrime c == qX * (pZ * pZ) % getPrime c) /\
    (pY * (qZ * qZ * qZ) % getPrime c == qY * (pZ * pZ * pZ) % getPrime c)))

let lemma_multiplication_is_pointEqual_r #c p q = 
  let prime = getPrime c in 

  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  
  let pNX, pNY, pNZ = _norm p in 
  let qNX, qNY, qNZ = _norm q in 

  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime pZ pZ;
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (pZ * pZ) pZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime qZ qZ; 
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero prime (qZ * qZ) qZ;

 
  if pNX = qNX then begin
    assert(pX * modp_inv2 #c (pZ * pZ) % prime * (pZ * pZ) * (qZ * qZ) % prime = qX * modp_inv2 #c (qZ * qZ) % prime * (pZ * pZ) * (qZ * qZ) % prime);
    lemma_multiplication_is_pointEqual_r0 #c p q;
    assert(qX * (pZ * pZ) % prime == pX * (qZ * qZ) % prime)
    end;

  assert(pNX == qNX ==> pX * (qZ * qZ) % prime == qX * (pZ * pZ) % prime );

  if pY * modp_inv2 #c (pZ * pZ * pZ) % prime = qY * modp_inv2 #c (qZ * qZ * qZ) % prime then begin
    assert(pY * modp_inv2 #c (pZ * pZ * pZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime = qY * modp_inv2 #c (qZ * qZ * qZ) % prime * (pZ * pZ * pZ) * (qZ * qZ * qZ) % prime);
    lemma_multiplication_is_pointEqual_r1 #c p q;
    assert ((pY * (qZ * qZ * qZ) % getPrime c == qY * (pZ * pZ * pZ) % getPrime c))
    end

 *)

(* 
The formulas for complete point addition for jacobian coordinates require a check for points not to be 
equal to each other. See more in : 

Weierstraß Elliptic Curves and Side-Channel Attacks Eric Brier and Marc Joye. 

Such way we don't provide a method to compute it, but the following code is used as a wrapper over the check of point equality,
followed by point double (if they are equal) or point add (otherwise).*)


let point_add_c #c p q result tempBuffer = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  
  let sq_z1 = sub tempBuffer (size 0) len in 
  let tr_z1 = sub tempBuffer len len in 
  
  let sq_z2 = sub tempBuffer (size 2 *! len) len in 
  let tr_z2 = sub tempBuffer (size 3 *! len) len in 

  let x1 = sub p (size 0) len in 
  let y1 = sub p len len in 
  let z1 = sub p (size 2 *! len) len in 

  let x2 = sub q (size 0) len in 
  let y2 = sub q len len in 
  let z2 = sub q (size 2 *! len) len in 

  montgomery_square_buffer_dh #c z1 sq_z1;
  montgomery_square_buffer_dh #c z2 sq_z2;

  montgomery_multiplication_buffer_dh #c sq_z1 z1 tr_z1;
  montgomery_multiplication_buffer_dh #c sq_z2 z2 tr_z2;

  montgomery_multiplication_buffer_dh #c sq_z1 x2 sq_z1;
  montgomery_multiplication_buffer_dh #c sq_z2 x1 sq_z2;

  montgomery_multiplication_buffer_dh #c tr_z1 y2 tr_z1;
  montgomery_multiplication_buffer_dh #c tr_z2 y1 tr_z2;

    let h2 = ST.get() in 

  let equalX = cmp_felem_felem_bool #c sq_z1 sq_z2 in 
  let equalY = cmp_felem_felem_bool #c tr_z1 tr_z2 in 

  let equalXAndY = equalX && equalY in 

  if equalXAndY then
   point_double p result tempBuffer
  else  
    point_add p q result tempBuffer;

    let h3 = ST.get() in 

  let x1D = fromDomain_ #c #DH (as_nat c h0 x1) in 
  let x2D = fromDomain_ #c #DH (as_nat c h0 x2) in 
  
  let y1D = fromDomain_ #c #DH (as_nat c h0 y1) in 
  let y2D = fromDomain_ #c #DH (as_nat c h0 y2) in 

  let z1D = fromDomain_ #c #DH (as_nat c h0 z1) in 
  let z2D = fromDomain_ #c #DH (as_nat c h0 z2) in 

  let prime = getPrime c in 

  lemma_mod_mul_distr_l (z1D * z1D) z1D prime;
  lemma_mod_mul_distr_l (z2D * z2D) z2D prime;

  lemma_mod_mul_distr_l (z1D * z1D) x2D prime;
  lemma_mod_mul_distr_l (z2D * z2D) x1D prime;

  lemma_mod_mul_distr_l (z1D * z1D * z1D) y2D prime;
  lemma_mod_mul_distr_l (z2D * z2D * z2D) y1D prime;

  lemma_modular_multiplication_2_d #c (z1D * z1D * x2D % prime) (z2D * z2D * x1D % prime);
  lemma_modular_multiplication_2_d #c (z1D * z1D * z1D * y2D % prime) (z2D * z2D * z2D * y1D % prime);

  lemma_pointAtInfInDomain #c (as_nat c h0 x1) (as_nat c h0 y1) (as_nat c h0 z1);
  lemma_pointAtInfInDomain #c (as_nat c h0 x2) (as_nat c h0 y2) (as_nat c h0 z2);

(*   lemma_multiplication_is_pointEqual_l #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) 
    (fromDomainPoint #c #DH (point_as_nat c h0 q)); *)
    
(*   lemma_multiplication_is_pointEqual_r #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) 
    (fromDomainPoint #c #DH (point_as_nat c h0 q)); *)

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  
  assert_by_tactic ((z1D * z1D * z1D) * y2D == y2D * (z1D * z1D * z1D)) canon;
  assert_by_tactic ((z2D * z2D * z2D) * y1D == y1D * (z2D * z2D * z2D)) canon



let point_add_c_out #c p q result = 
  let h0 = ST.get() in 
  push_frame();
    let tempBuffer = create (size 17 *! getCoordinateLenU64 c) (u64 0) in 
    let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 q;
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
    point_add_c p q result tempBuffer;
  let h2 = ST.get() in 
  pop_frame();
  let h3 = ST.get() in 
     Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h2 h3 result

  
