module Hacl.Impl.P.PointAddMixed.Aux

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Spec.ECC
open Spec.ECC.Curves

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

open Hacl.Spec.MontgomeryMultiplication
open Hacl.Spec.EC.Definition

open FStar.Mul
open Hacl.Impl.P.PointAdd.Aux 



#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"  


let u1Invariant (#c: curve) (h0: mem) (h1: mem) (u1: felem c) (p: point c) =  
  point_eval c h0 p /\ (
  let pxD = fromDomain #c (point_x_as_nat c h0 p) in 
  felem_eval c h1 u1 /\ as_nat c h1 u1 == toDomain #c (fromDomain #c 1 * fromDomain #c 1 * pxD % getPrime c))


let u2Invariant (#c: curve) (h0: mem) (h1: mem) (u2: felem c) (p: point c) (q: pointAffine c)  =  
  point_eval c h0 p /\ point_aff_eval c h0 q /\ (
  let pzD = fromDomain #c (point_z_as_nat c h0 p) in 
  let qxD = fromDomain #c (point_affine_x_as_nat c h0 q) in 
  felem_eval c h1 u2 /\ as_nat c h1 u2 == toDomain #c (pzD * pzD * qxD % getPrime c))


let s1Invariant (#c: curve) (h0: mem) (h1: mem) (s1: felem c) (p: point c) = 
  point_eval c h0 p /\ (
  let pyD = fromDomain #c (point_y_as_nat c h0 p) in 
  let oD = fromDomain #c 1 in 
  felem_eval c h1 s1 /\ as_nat c h1 s1 == toDomain #c (oD * oD * oD * pyD % getPrime c))


let s2Invariant (#c: curve) (h0: mem) (h1: mem) (s2: felem c) (p: point c) (q: pointAffine c)  = 
  point_eval c h0 p /\ point_aff_eval c h0 q /\ (
  let pzD = fromDomain #c (point_z_as_nat c h0 p) in 
  let qyD = fromDomain #c (point_affine_y_as_nat c h0 q) in 
  felem_eval c h1 s2 /\ as_nat c h1 s2 == toDomain #c (pzD * pzD * pzD * qyD % getPrime c))


let z3Invariant (#c: curve) (h0: mem) (h1: mem) (z3: felem c) (z1: felem c) (h: felem c) = 
  let z1D = fromDomain #c (as_nat c h0 z1) in 
  let hD = fromDomain #c (as_nat c h0 h) in 
  felem_eval c h1 z3 /\
  as_nat c h1 z3 == toDomain #c (z1D * fromDomain #c 1 * hD % getPrime c)


val point_affine_x_modifies_lemma: c: curve -> h0: mem -> h1: mem -> q: pointAffine c -> 
  Lemma (requires (point_aff_eval c h0 q /\ as_seq h0 q == as_seq h1 q))
  (ensures (point_affine_x_as_nat c h0 q == point_affine_x_as_nat c h1 q))

let point_affine_x_modifies_lemma c h0 h1 q = ()

val point_affine_y_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: pointAffine c -> 
  Lemma (requires (point_aff_eval c h0 q /\ as_seq h0 q == as_seq h1 q))
  (ensures (point_affine_y_as_nat c h0 q == point_affine_y_as_nat c h1 q))

let point_affine_y_modifies_lemma c h0 h1 q = ()

val lemma_point_affine_eval: c: curve -> h0: mem -> h1: mem -> p: pointAffine c -> Lemma
  (requires (point_aff_eval c h0 p /\ as_seq h0 p == as_seq h1 p))
  (ensures (point_aff_eval c h1 p))

let lemma_point_affine_eval c h0 h1 p = 
  point_affine_x_modifies_lemma c h0 h1 p;
  point_affine_y_modifies_lemma c h0 h1 p


val lemma_coord_affine_eval: c: curve -> h0: mem -> h1 : mem -> p: pointAffine c -> 
  Lemma 
  (requires (point_aff_eval c h0 p /\ as_seq h1 p == as_seq h0 p))
  (ensures (point_aff_eval c h1 p /\ 
    point_affine_as_nat c h0 p  == point_affine_as_nat c h1 p /\
    point_affine_x_as_nat c h0 p == point_affine_x_as_nat c h1 p /\
    point_affine_y_as_nat c h0 p == point_affine_y_as_nat c h1 p))  

let lemma_coord_affine_eval c h0 h1 p = ()

val lemma_point_add_if: #c: curve -> p: point c -> q: pointAffine c  -> result: point c
  -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) 
  -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c -> 
  h0: mem -> h1: mem -> h2: mem ->
  Lemma
    (requires (
    let z1 = getZ p in 
    let x3_out, y3_out, z3_out = getXYZ #c t5 in 
    point_eval c h0 p /\ point_aff_eval c h0 q /\ point_eval c h2 result /\
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h /\
    x3Invariant #c h0 h1 x3_out r hCube uh  /\
    y3Invariant #c h0 h1 y3_out s1 hCube uh x3_out r /\ 
    z3Invariant #c h0 h1 z3_out z1 h /\ (
    
    if point_affine_x_as_nat c h0 q = 0 && point_affine_y_as_nat c h0 q = 0 then 
      point_x_as_nat c h2 result == point_x_as_nat c h0 p /\
      point_y_as_nat c h2 result == point_y_as_nat c h0 p /\ 
      point_z_as_nat c h2 result == point_z_as_nat c h0 p
    else if point_z_as_nat c h0 p = 0 then 
      point_x_as_nat c h2 result == point_affine_x_as_nat c h0 q /\
      point_y_as_nat c h2 result == point_affine_y_as_nat c h0 q /\ 
      point_z_as_nat c h2 result == 1
    else 
      point_x_as_nat c h2 result == as_nat c h1 x3_out /\ 
      point_y_as_nat c h2 result == as_nat c h1 y3_out /\ 
      point_z_as_nat c h2 result == as_nat c h1 z3_out)))
  (ensures (
    let prime = getPrime c in 

    let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q, 1 in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  
    
    if qxD = 0 && qyD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD 
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain #c x3) * rD - s1D * hD * hD * hD) % prime)  /\
      z3 == toDomain #c (pzD * qzD * hD % prime)))



let lemma_point_add_if #c p q result t5 u1 u2 s1 s2 r h uh hCube h0 h1 h2 = 
  let prime = getPrime c in 
  let fromDomain = fromDomain #c in 
  
  let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
  let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
  let qX, qY, qZ = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q, 1 in 

  let pxD, pyD, pzD = fromDomain pX, fromDomain pY, fromDomain pZ in 
  let qxD, qyD, qzD = fromDomain qX, fromDomain qY, fromDomain qZ in 
  let x3D, y3D, z3D = fromDomain x3, fromDomain y3, fromDomain z3 in 

  Hacl.Impl.EC.Math.lemma_multiplication_not_mod_prime #c (point_affine_x_as_nat c h0 q);
  Hacl.Impl.EC.Math.lemma_multiplication_not_mod_prime #c (point_affine_y_as_nat c h0 q);
  Hacl.Impl.EC.Math.lemma_multiplication_not_mod_prime #c (point_z_as_nat c h0 p); 

  lemmaFromDomain #c #DH (point_z_as_nat c h0 p);
  lemmaFromDomain #c #DH (point_affine_x_as_nat c h0 q);
  lemmaFromDomain #c #DH (point_affine_y_as_nat c h0 q);

  assert(point_affine_x_as_nat c h0 q = 0 <==> fromDomain (point_affine_x_as_nat c h0 q) = 0);
  assert(point_affine_y_as_nat c h0 q = 0 <==> fromDomain (point_affine_y_as_nat c h0 q) = 0);
  assert(point_z_as_nat c h0 p = 0 <==> fromDomain (point_z_as_nat c h0 p) = 0);

 
  let rD = fromDomain (as_nat c h0 r) in  
  let hD = fromDomain (as_nat c h0 h) in 
  let s1D = fromDomain (as_nat c h0 s1) in 
  let u1D = fromDomain (as_nat c h0 u1) in 

  let uhD = fromDomain (as_nat c h0 uh) in 
  let hCubeD = fromDomain (as_nat c h0 hCube) in 

  calc (==)
  {
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D % prime)) % prime;
    (==) {lemma_mod_sub_distr (rD * rD - (hD * hD * hD % prime)) (2 * (hD * hD * u1D % prime)) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r 2 (hD * hD * u1D) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D) % prime) % prime;
    (==) {_ by (canon())}
    (rD * rD - (hD * hD * hD % prime) - 2 * hD * hD * u1D % prime) % prime;
    (==) {lemma_mod_sub_distr (rD * rD - (hD * hD * hD % prime)) (2 * hD * hD * u1D) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * hD * hD * u1D) % prime;
    (==) {_ by (canon())}
    (rD * rD  - 2 * hD * hD * u1D - (hD * hD * hD % prime)) % prime;
    (==) {lemma_mod_sub_distr (rD * rD -  2 * hD * hD * u1D) (hD * hD * hD) prime}
    (rD * rD  - 2 * hD * hD * u1D - hD * hD * hD) % prime;
    (==) {_ by (canon())}
    (rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime;
  };

  let x3D = fromDomain (point_x_as_nat c h2 result) in 
  let rh = s1D * hD * hD * hD in
  let lh = hD * hD * u1D in 

  calc (==)
  {
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD % prime)) % prime;
    (==) {lemma_mod_sub_distr (((hD * hD * u1D % prime) - x3D) * rD) (s1D * (hD * hD * hD % prime)) prime}
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r s1D (hD * hD * hD) prime}
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD) % prime) % prime;
    (==) {_ by (canon()) }
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * hD * hD * hD % prime) % prime;
    (==) {lemma_mod_sub_distr (((hD * hD * u1D % prime) - x3D) * rD) (s1D * hD * hD * hD) prime}
    ((((lh % prime) - x3D) * rD) - rh) % prime;
    (==) {_ by (canon())}
    (-rh + (((lh % prime) - x3D) * rD)) % prime;
    (==) {lemma_mod_add_distr (-rh) (((lh % prime) - x3D) * rD) prime}
    (-rh + (((lh % prime) - x3D) * rD) % prime) % prime;
    (==) {lemma_mod_mul_distr_l ((lh % prime) - x3D) rD prime}
    (-rh + (((lh % prime) - x3D) % prime * rD) % prime) % prime;
    (==) {_ by (canon())} 
    (-rh + ((-x3D + (lh % prime)) % prime * rD) % prime) % prime;
    (==) {lemma_mod_add_distr (-x3D) lh prime}
    (-rh + ((-x3D + lh) % prime * rD) % prime) % prime;
    (==) {lemma_mod_mul_distr_l (-x3D + lh) rD prime}
    (-rh + ((-x3D + lh) * rD) % prime) % prime;
    (==) {_ by (canon())}
    (-rh + ((lh - x3D) * rD) % prime) % prime;
    (==) {lemma_mod_add_distr (-rh) ((lh - x3D) * rD) prime}
    (-rh + (lh - x3D) * rD) % prime;
    (==) {_ by (canon())}
    ((lh - x3D) * rD - rh) % prime;
    (==) {}
    ((hD * hD * u1D - x3D) * rD - s1D * hD * hD * hD) % prime;}
