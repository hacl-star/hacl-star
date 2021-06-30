module Spec.P256.MontgomeryMultiplication.PointAdd

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Spec.P256.Definitions

open Lib.Sequence

open Spec.P256.MontgomeryMultiplication
open FStar.Mul
open Spec.P256


let prime = prime256

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"  

       
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
     
    u1 == toDomain_ (qzD * qzD * pxD % prime256) /\ u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
    s1 == toDomain_ (qzD * qzD * qzD * pyD % prime256) /\ s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256) /\
    h == toDomain_ ((u2D - u1D) % prime256) /\ r == toDomain_ ((s2D - s1D) % prime256) /\ (
    if qzD = 0 then 
      fromDomain_ x3 == pxD /\ fromDomain_ y3 == pyD /\ fromDomain_ z3 == pzD
    else if pzD = 0 then 
      fromDomain_ x3 == qxD /\  fromDomain_ y3 == qyD /\  fromDomain_ z3 == qzD 
    else
      x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\
      y3 == toDomain_ (((hD * hD * u1D - x3D) * rD - s1D * hD*hD*hD) % prime) /\
      z3 == toDomain_ ((pzD * qzD * hD) % prime))))
  (ensures (    
    let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 
    let (xN, yN, zN) = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in
    let u1D = fromDomain_ u1 in let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in let s2D = fromDomain_ s2 in 
    xN == x3D /\  yN == y3D /\ zN == z3D))

let lemma_pointAddToSpecification x1D y1D z1D x2D y2D z2D x3 y3 z3  u1 u2 s1 s2 h r = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
   
  let u1D = fromDomain_ u1 in 
  let u2D = fromDomain_ u2 in 
  let s1D = fromDomain_ s1 in 
  let s2D = fromDomain_ s2 in 

  let hD = fromDomain_ h in 
  let rD = fromDomain_ r in 

  let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 

  let pxD, pyD, pzD = x1D, y1D, z1D in 
  let qxD, qyD, qzD = x2D, y2D, z2D in 


    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 


    assert_by_tactic (z2D * z2D * pxD = pxD * (z2D * z2D)) canon; 
    assert_by_tactic (z1D * z1D * x2D == x2D * (z1D * z1D)) canon;

    assert_by_tactic (z2D * z2D * z2D * y1D = y1D * z2D * (z2D * z2D)) canon;
    assert_by_tactic (z1D * z1D * z1D * y2D = y2D * z1D * (z1D * z1D)) canon;

  let z2z2 = z2D * z2D in
  let z1z1 = z1D * z1D in

  let u1 = x1D * z2z2 % prime256 in
  let u2 = x2D * z1z1 % prime256 in

  let s1 = y1D * z2D * z2z2 % prime256 in
  let s2 = y2D * z1D * z1z1 % prime256 in

  assert(u1 == u1D);
  assert(u2 == u2D);
  assert(s1 == s1D);
  assert(s2 == s2D);

  let h = (u2 - u1) % prime256 in
  assert(h == hD);
  
  let r = (s2 - s1) % prime256 in
  assert(r == rD);

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3_ = (r * r - h * h * h - 2 * u1 * hh) % prime256 in 
    assert_by_tactic (2 * u1 * (h * h) == 2 * h * h * u1) canon;

  let y3_ = (r * (u1 * (h * h) - x3_) - s1 * (h * h * h)) % prime256 in
    assert_by_tactic ((h * h * u1 - x3_) == (u1 * (h * h) - x3_)) canon;
    assert_by_tactic ((r * (h * h * u1 - x3_) - s1 * (h * h * h)) = ((h * h * u1 - x3_) * r - s1 * h * h * h)) canon; 

  let z3_ = (h * z1D * z2D) % prime256 in 
    
    assert_by_tactic (z1D * z2D * hD = hD * z1D * z2D) canon;

  if z2D = 0 then
    assert(xN == x1D /\ yN == y1D /\ zN == z1D)
  else
    if z1D = 0 then
      assert(xN == x2D /\ yN == y2D /\ zN == z2D)
    else
      assert(xN == x3_ /\ yN == y3_ /\ zN == z3_)
      

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
