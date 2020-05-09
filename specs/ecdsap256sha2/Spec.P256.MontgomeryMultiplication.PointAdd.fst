module Spec.P256.MontgomeryMultiplication.PointAdd

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Spec.P256.Definitions

open Lib.Sequence

open Spec.P256.MontgomeryMultiplication
open FStar.Mul
open Spec.P256

open Spec.P256.MontgomeryMultiplication.PointDouble

let prime = prime256

#set-options "--z3rlimit 100"  

noextract       
val lemma_pointAddToSpecification: 
  pxD: nat {pxD < prime256} -> pyD: nat{pyD < prime256} -> pzD: nat {pzD < prime256} -> 
  qxD: nat {qxD < prime256} -> qyD: nat {qyD < prime256} -> qzD: nat {qzD < prime256} -> 
  x3: nat -> y3: nat -> z3: nat -> 
  u1: nat -> u2: nat -> s1: nat -> s2: nat -> 
  h: nat -> r: nat -> 
  Lemma
    (requires (    
      let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 

      let u1D, u2D = fromDomain_ u1, fromDomain_ u2 in 
      let s1D, s2D = fromDomain_ s1, fromDomain_ s2 in 
      let rD = fromDomain_ r in    
      let hD = fromDomain_ h in 
     
      u1 == toDomain_ (qzD * qzD * pxD % prime256) /\
      u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
      s1 == toDomain_ (qzD * qzD * qzD * pyD % prime256) /\
      s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256) /\
      
      h == toDomain_ ((u2D - u1D) % prime256) /\
      r == toDomain_ ((s2D - s1D) % prime256) /\
      (
	if qzD = 0 then 
	  fromDomain_ x3 == pxD /\ fromDomain_ y3 == pyD /\ fromDomain_ z3 == pzD
	else if pzD = 0 then 
	    fromDomain_ x3 == qxD /\  fromDomain_ y3 == qyD /\  fromDomain_ z3 == qzD 
	else
	    x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\
	    y3 == toDomain_ (((hD * hD * u1D - x3D) * rD - s1D * hD*hD*hD) % prime) /\
	    z3 == toDomain_ ((pzD * qzD * hD) % prime)
	)
      )
  )
  (ensures 
  (    
    let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 
    let (xN, yN, zN) = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in
    let u1D = fromDomain_ u1 in let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in let s2D = fromDomain_ s2 in 
    xN == x3D /\  yN == y3D /\ zN == z3D
  )
)

val lemma_pointAdd0: a: nat -> b: nat -> Lemma (2 * a * a * b == 2 * b * a * a)

let lemma_pointAdd0 a b = ()


let lemma_pointAddToSpecification x1D y1D z1D x2D y2D z2D x3 y3 z3  u1 u2 s1 s2 h r = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
   
    let u1D = fromDomain_ u1 in 
    let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in 
    let s2D = fromDomain_ s2 in 

    let hD = fromDomain_ h in 
    let rD = fromDomain_ r in 
    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 

    let u1N = x1D * z2D * z2D % prime in
    let u2N = x2D * z1D * z1D % prime in 
    let s1N = y1D * z2D * z2D * z2D % prime in 
    let s2N = y2D * z1D * z1D * z1D % prime in 

    let hN = (u2N - u1N) % prime in 
    let rN = (s2N - s1N) % prime in 

    assert_by_tactic (x1D * z2D * z2D = (z2D * z2D) * x1D) canon;
    assert_by_tactic (x1D * (z2D * z2D) == z2D * z2D * x1D) canon;
    
    assert_by_tactic (x2D * z1D * z1D = x2D * (z1D * z1D)) canon;
    assert_by_tactic (z1D * z1D * x2D = x2D * (z1D * z1D)) canon;

    assert_by_tactic (z2D * z2D * z2D * y1D = y1D * z2D * (z2D * z2D)) canon;  
    assert_by_tactic (z1D * z1D * z1D * y2D = y2D * z1D * (z1D * z1D)) canon;

    assert_by_tactic (z1D * z2D * hD = hD * z1D * z2D) canon;
    assert_by_tactic ((rD * (u1D * (hD * hD) - xN) - s1D * (hD * hD * hD)) = ((hD * hD * u1D - xN) * rD - s1D * hD*hD*hD)) canon;
    
    assert_by_tactic (forall (n: nat). n * hN * hN = n * (hN * hN)) canon;
    lemma_pointAdd0 hD u1D


val lemma_point_add_0: a: int -> b: int -> c: int -> Lemma 
  ((a - b - 2 * (c % prime256)) % prime256 == (a - b - 2 * c) % prime256)

let lemma_point_add_0 a b c = 
  lemma_mod_sub_distr (a - b) (2 * (c % prime256)) prime256;
  lemma_mod_mul_distr_r 2 c prime256;
  lemma_mod_sub_distr (a - b) (2 * c) prime256


val lemma_point_add_1: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma
  ((((a % prime256) - b) * c - d * (e % prime256)) % prime256 == ((a - b) * c - d * e) % prime256)

let lemma_point_add_1 a b c d e = 
  lemma_mod_add_distr (- d * (e % prime256)) (((a % prime256) - b) * c) prime256;
  lemma_mod_mul_distr_l ((a % prime256) - b) c prime256;
  lemma_mod_add_distr (-b) a prime256;
  lemma_mod_mul_distr_l (a - b) c prime256;
  lemma_mod_add_distr (- d * (e % prime256)) ((a - b) * c) prime256;
  
  lemma_mod_sub_distr ((a - b) * c) (d * (e % prime256)) prime256;
  lemma_mod_mul_distr_r d e prime256;
  lemma_mod_sub_distr ((a - b) * c) (d * e) prime256
