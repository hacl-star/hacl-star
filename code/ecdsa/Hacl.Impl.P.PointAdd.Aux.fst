module Hacl.Impl.P.PointAdd.Aux


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


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"  


val getXYZ: #c: curve -> lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> GTot (tuple3 (felem c) (felem c) (felem c))
  
let getXYZ #c t5 = 
  let len = getCoordinateLenU64 c in 
  
  let x3_out = gsub t5 (size 0) len in 
  let y3_out = gsub t5 len len in 
  let z3_out = gsub t5 (size 2 *! len) len in 
  (x3_out, y3_out, z3_out)


val getU1S2: #c: curve -> lbuffer uint64 (size 8 *! getCoordinateLenU64 c) -> GTot (tuple4 (felem c) (felem c) (felem c) (felem c))
  
let getU1S2 #c t8 = 
  let len = getCoordinateLenU64 c in 
  
  let u1 = gsub t8 (size 4 *! len) len in 
  let u2 = gsub t8 (size 5 *! len) len in 
  let s1 = gsub t8 (size 6 *! len) len in 
  let s2 = gsub t8 (size 7 *! len) len in 

  (u1, u2, s1, s2)


val getHHCube : #c: curve -> lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> GTot (tuple4 (felem c) (felem c) (felem c) (felem c))

let getHHCube #c t4 = 
  let len = getCoordinateLenU64 c in 
  let u1 = gsub t4 (size 0) len in 
  let u2 = gsub t4 len len in 
  let s1 = gsub t4 (size 2 *! len) len in 
  let s2 = gsub t4 (size 3 *! len) len in 
  
  (u1, u2, s1, s2)


val getU1HCube: #c: curve -> lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  GTot (tuple8 (felem c) (felem c) (felem c) (felem c) (felem c) (felem c) (felem c) (felem c))

let getU1HCube #c tempBuffer12 = 
  let len = getCoordinateLenU64 c in 

  let u1 = gsub tempBuffer12 (size 4 *! len) len in 
  let u2 = gsub tempBuffer12 (size 5 *! len) len in 
  let s1 = gsub tempBuffer12 (size 6 *! len) len in 
  let s2 = gsub tempBuffer12 (size 7 *! len) len in 
  
  let h = gsub tempBuffer12 (size 8 *! len) len in 
  let r = gsub tempBuffer12 (size 9 *! len) len in 
  let uh = gsub tempBuffer12 (size 10 *! len) len in 
  let hCube = gsub tempBuffer12 (size 11 *! len) len in 

  (u1, u2, s1, s2, h, r, uh, hCube)


let u1Invariant (#c: curve) (h0: mem) (h1: mem) (u1: felem c) (p: point c) (q: point c)  =  
  let pxD = fromDomain #c (point_x_as_nat c h0 p) in 
  let qzD = fromDomain #c (point_z_as_nat c h0 q) in 
  felem_eval c h1 u1 /\ as_nat c h1 u1 == toDomain #c (qzD * qzD * pxD % getPrime c)


let u2Invariant (#c: curve) (h0: mem) (h1: mem) (u2: felem c) (p: point c) (q: point c)  =  
  let pzD = fromDomain #c (point_z_as_nat c h0 p) in 
  let qxD = fromDomain #c (point_x_as_nat c h0 q) in 
  felem_eval c h1 u2 /\ as_nat c h1 u2 == toDomain #c (pzD * pzD * qxD % getPrime c)


let s1Invariant (#c: curve) (h0: mem) (h1: mem) (s1: felem c) (p: point c) (q: point c)  = 
  let pyD = fromDomain #c (point_y_as_nat c h0 p) in 
  let qzD = fromDomain #c (point_z_as_nat c h0 q) in 
  felem_eval c h1 s1 /\ as_nat c h1 s1 == toDomain #c (qzD * qzD * qzD * pyD % getPrime c)


let s2Invariant (#c: curve) (h0: mem) (h1: mem) (s2: felem c) (p: point c) (q: point c)  = 
  let pzD = fromDomain #c (point_z_as_nat c h0 p) in 
  let qyD = fromDomain #c (point_y_as_nat c h0 q) in 
  felem_eval c h1 s2 /\ as_nat c h1 s2 == toDomain #c (pzD * pzD * pzD * qyD % getPrime c)


let hInvariant (#c: curve) (h0: mem) (h: felem c) (u1: felem c) (u2: felem c) = 
  let u1D = fromDomain #c (as_nat c h0 u1) in 
  let u2D = fromDomain #c (as_nat c h0 u2) in 
  felem_eval c h0 h /\ as_nat c h0 h == toDomain #c ((u2D - u1D) % getPrime c)

let rInvariant (#c: curve) (h0: mem) (r: felem c) (s1: felem c) (s2: felem c)  = 
  let s1D = fromDomain #c (as_nat c h0 s1) in 
  let s2D = fromDomain #c (as_nat c h0 s2) in 
  felem_eval c h0 r /\ as_nat c h0 r == toDomain #c ((s2D - s1D) % getPrime c) 

let uhInvariant (#c: curve) (h0: mem) (uh: felem c) (h: felem c) (u1: felem c) = 
  let hD = fromDomain #c (as_nat c h0 h) in 
  let u1D = fromDomain #c (as_nat c h0 u1) in 
  felem_eval c h0 uh /\ as_nat c h0 uh == toDomain #c (hD * hD * u1D % getPrime c) 

let hCubeInvariant (#c: curve) (h0 : mem) (hCube: felem c) (h: felem c) = 
  let hD = fromDomain #c (as_nat c h0 h) in 
  felem_eval c h0 hCube /\ as_nat c h0 hCube == toDomain #c (hD * hD * hD % getPrime c)


val lemma_ICuttable_common: #c: curve -> Lemma (
    let len = getCoordinateLenU64 c in 
    v (size 0) + v (size 4 *! len) <= v (size 12 *! len) /\
    v (size 4 *! len) + v len <= v (size 12 *! len) /\
    v (size 5 *! len) + v len <= v (size 12 *! len) /\
    v (size 6 *! len) + v len <= v (size 12 *! len) /\
    v (size 7 *! len) + v len <= v (size 12 *! len) /\
    v (size 8 *! len) + v len <= v (size 12 *! len) /\
    v (size 9 *! len) + v len <= v (size 12 *! len) /\
    v (size 10 *! len) + v len <= v (size 12 *! len) /\
    v (size 11 *! len) + v len <= v (size 12 *! len))
	
let lemma_ICuttable_common #c = ()



let x3Invariant (#c: curve) (h0: mem) (h1: mem) (x3: felem c) (r: felem c) (hCube: felem c) (uh: felem c) = 
  let hCubeD = fromDomain #c (as_nat c h0 hCube) in 
  let uhD = fromDomain #c (as_nat c h0 uh) in 
  let rD = fromDomain #c (as_nat c h0 r) in 
  felem_eval c h1 x3 /\ as_nat c h1 x3 == toDomain #c ((rD * rD - hCubeD - 2 * uhD) % getPrime c)


let y3Invariant (#c: curve) (h0: mem) (h1: mem) (y3: felem c) (s1: felem c) (hCube: felem c) (uh: felem c) (x3: felem c) (r: felem c) = 
  let s1D = fromDomain #c (as_nat c h0 s1) in 
  let hCubeD = fromDomain #c (as_nat c h0 hCube) in 
  let uhD = fromDomain #c (as_nat c h0 uh) in 
  let rD = fromDomain #c (as_nat c h0 r) in 

  let x3D = fromDomain #c (as_nat c h1 x3) in 
  felem_eval c h1 y3 /\ 
  as_nat c h1 y3 = toDomain #c (((uhD - x3D) * rD - s1D * hCubeD) % getPrime c)




let z3Invariant (#c: curve) (h0: mem) (h1: mem) (z3: felem c) (z1: felem c) (z2: felem c) (h: felem c) = 
  let z1D = fromDomain #c (as_nat c h0 z1) in 
  let z2D = fromDomain #c (as_nat c h0 z2) in 
  let hD = fromDomain #c (as_nat c h0 h) in 
  felem_eval c h1 z3 /\ 
  as_nat c h1 z3 == toDomain #c (z1D * z2D * hD % getPrime c)



val point_x_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_x_as_nat c h0 q == point_x_as_nat c h1 q))

let point_x_modifies_lemma c h0 h1 q = ()

val point_y_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_y_as_nat c h0 q == point_y_as_nat c h1 q))

let point_y_modifies_lemma c h0 h1 q = ()

val point_z_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_z_as_nat c h0 q == point_z_as_nat c h1 q))

let point_z_modifies_lemma c h0 h1 q = 
  assert(as_nat c h0 (gsub q (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) == 
    as_nat c h1 (gsub q (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)))


val lemma_point_eval: c: curve -> h0: mem -> h1: mem -> p: point c -> Lemma
  (requires (point_eval c h0 p /\ as_seq h0 p == as_seq h1 p))
  (ensures (point_eval c h1 p))


val lemma_coord_eval: c: curve -> h0: mem -> h1 : mem -> p: point c -> 
  Lemma 
    (requires (as_seq h1 p == as_seq h0 p))
    (ensures (
      point_x_as_nat c h0 p == point_x_as_nat c h1 p /\
      point_y_as_nat c h0 p == point_y_as_nat c h1 p /\
      point_z_as_nat c h0 p == point_z_as_nat c h1 p))  


let lemma_point_eval c h0 h1 p = 
  point_x_modifies_lemma c h0 h1 p;
  point_y_modifies_lemma c h0 h1 p;
  point_z_modifies_lemma c h0 h1 p


let lemma_coord_eval c h0 h1 p = 
  let len = getCoordinateLenU64 c in 
  let f = gsub p (size 2 *! len) len in 
  assert(as_nat c h0 f == as_nat c h1 f)




val lemma_point_add_if_0: #c: curve -> p: point c -> result: point c 
  -> h0: mem {point_eval c h0 p} 
  -> h2: mem {point_eval c h2 result}
  -> 
  Lemma (	
    (point_x_as_nat c h2 result == point_x_as_nat c h0 p <==> fromDomain #c (point_x_as_nat c h2 result) == fromDomain #c (point_x_as_nat c h0 p)) /\
    (point_x_as_nat c h2 result == point_x_as_nat c h0 p <==> fromDomain #c (point_x_as_nat c h2 result) == fromDomain #c (point_x_as_nat c h0 p)) /\
    (point_x_as_nat c h2 result == point_x_as_nat c h0 p <==> fromDomain #c (point_x_as_nat c h2 result) == fromDomain #c (point_x_as_nat c h0 p)))


let lemma_point_add_if_0 #c p result h0 h2 = 
  lemmaFromDomain #c #DH (point_x_as_nat c h0 p);
  lemmaFromDomain #c #DH (point_x_as_nat c h2 result);
  Hacl.Impl.EC.Math.lemma_modular_multiplication #c (point_x_as_nat c h0 p) (point_x_as_nat c h2 result);

  lemmaFromDomain #c #DH (point_y_as_nat c h0 p);
  lemmaFromDomain #c #DH (point_y_as_nat c h2 result);
  Hacl.Impl.EC.Math.lemma_modular_multiplication #c (point_y_as_nat c h0 p) (point_y_as_nat c h2 result);

  lemmaFromDomain #c #DH (point_z_as_nat c h2 result);
  Hacl.Impl.EC.Math.lemma_modular_multiplication #c (point_z_as_nat c h0 p) (point_z_as_nat c h2 result)



val lemma_point_add_if: #c: curve -> p: point c -> q: point c  -> result: point c
  -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) 
  -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c -> 
  h0: mem -> h1: mem -> h2: mem ->
  Lemma
    (requires (
    let z1, z2 = getZ p, getZ q in 
    let x3_out, y3_out, z3_out = getXYZ #c t5 in 
    point_eval c h0 p /\ point_eval c h0 q /\ 
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h /\
    x3Invariant #c h0 h1 x3_out r hCube uh  /\
    y3Invariant #c h0 h1 y3_out s1 hCube uh x3_out r /\ 
    z3Invariant #c h0 h1 z3_out z1 z2 h /\ (
    
    if point_z_as_nat c h0 q = 0 then 
      point_x_as_nat c h2 result == point_x_as_nat c h0 p /\
      point_y_as_nat c h2 result == point_y_as_nat c h0 p /\ 
      point_z_as_nat c h2 result == point_z_as_nat c h0 p
    else if point_z_as_nat c h0 p = 0 then 
      point_x_as_nat c h2 result == point_x_as_nat c h0 q /\
      point_y_as_nat c h2 result == point_y_as_nat c h0 q /\ 
      point_z_as_nat c h2 result == point_z_as_nat c h0 q
    else 
      point_x_as_nat c h2 result == as_nat c h1 x3_out /\ 
      point_y_as_nat c h2 result == as_nat c h1 y3_out /\ 
      point_z_as_nat c h2 result == as_nat c h1 z3_out))
      )
  (ensures (
  (
    let prime = getPrime c in 

    let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  
    
    if qzD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD 
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain #c x3) * rD - s1D * hD * hD * hD) % prime)  /\
      z3 == toDomain #c (pzD * qzD * hD % prime))))



let lemma_point_add_if #c p q result t5 u1 u2 s1 s2 r h uh hCube h0 h1 h2 = 
  let prime = getPrime c in 
  let fromDomain = fromDomain #c in 
  
  let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
  let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
  let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

  let pxD, pyD, pzD = fromDomain pX, fromDomain pY, fromDomain pZ in 
  let qxD, qyD, qzD = fromDomain qX, fromDomain qY, fromDomain qZ in 
  let x3D, y3D, z3D = fromDomain x3, fromDomain y3, fromDomain z3 in 

  lemma_point_add_if_0 #c p result h0 h2;
  lemma_point_add_if_0 #c q result h0 h2;


(*   Hacl.Impl.EC.Math.lemma_multiplication_not_mod_prime #c (point_z_as_nat c h0 q);
  Hacl.Impl.EC.Math.lemma_multiplication_not_mod_prime #c (point_z_as_nat c h0 p); *)

  lemmaFromDomain #c #DH (point_z_as_nat c h0 p);
  lemmaFromDomain #c #DH (point_z_as_nat c h0 q);
  
  assert(point_z_as_nat c h0 q = 0 <==> fromDomain (point_z_as_nat c h0 q) = 0);
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


val lemma_ICuttable_point_add0: #c: curve  -> Lemma (
  let len = getCoordinateLenU64 c in 
  v (size 4 *! len) + v len <= v (size 8 *! len) /\
  v (size 5 *! len) + v len <= v (size 8 *! len) /\
  v (size 6 *! len) + v len <= v (size 8 *! len) /\
  v (size 7 *! len) + v len <= v (size 8 *! len))

let lemma_ICuttable_point_add0 #c = ()


(* To combine them to one? *)
val l_main: #c: curve -> a: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> h0: mem -> 
  Lemma (
    let len = getCoordinateLenU64 c in 
    let a0 = gsub a (size 0) (size 8 *! len) in 
    let a1 = gsub a (size 8 *! len) (size 4 *! len) in 

    gsub a (size 0 *! len) len == gsub a0 (size 0) len /\
    gsub a (size 1 *! len) len == gsub a0 (size 1 *! len) len /\
    gsub a (size 2 *! len) len == gsub a0 (size 2 *! len) len /\
    gsub a (size 3 *! len) len == gsub a0 (size 3 *! len) len /\
    gsub a (size 4 *! len) len == gsub a0 (size 4 *! len) len /\
    gsub a (size 5 *! len) len == gsub a0 (size 5 *! len) len /\
    gsub a (size 6 *! len) len == gsub a0 (size 6 *! len) len /\
    gsub a (size 7 *! len) len == gsub a0 (size 7 *! len) len /\
    
    gsub a (size 8 *! len) len == gsub a1 (size 0) len /\
    gsub a (size 9 *! len) len == gsub a1 (size 1 *! len) len /\
    gsub a (size 10 *! len) len == gsub a1 (size 2 *! len) len /\
    gsub a (size 11 *! len) len == gsub a1 (size 3 *! len) len)

let l_main #c a h0 = 
  let len = getCoordinateLenU64 c in 
  let a0 = gsub a (size 0) (size 8 *! len) in 
  let a1 = gsub a (size 8 *! len) (size 4 *! len) in 

  assert(gsub a (size 0 *! len) len == gsub a0 (size 0) len);
  assert(gsub a (size 1 *! len) len == gsub a0 (size 1 *! len) len);
  assert(gsub a (size 2 *! len) len == gsub a0 (size 2 *! len) len);
  assert(gsub a (size 3 *! len) len == gsub a0 (size 3 *! len) len);
  assert(gsub a (size 4 *! len) len == gsub a0 (size 4 *! len) len);
  assert(gsub a (size 5 *! len) len == gsub a0 (size 5 *! len) len);
  assert(gsub a (size 6 *! len) len == gsub a0 (size 6 *! len) len);
  assert(gsub a (size 7 *! len) len == gsub a0 (size 7 *! len) len);

  assert(gsub a (size 8 *! len) len == gsub a1 (size 0) len);
  assert(gsub a (size 9 *! len) len == gsub a1 (size 1 *! len) len);
  assert(gsub a (size 10 *! len) len == gsub a1 (size 2 *! len) len);
  assert(gsub a (size 11 *! len) len == gsub a1 (size 3 *! len) len)



val l0: #c: curve -> a: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> h0: mem -> p: point c 
  -> q: point c ->
  Lemma (
    let a0 = gsub a (size 0) (size 8 *! getCoordinateLenU64 c) in 
    let a1 = gsub a (size 8 *! getCoordinateLenU64 c) (size 4 *! getCoordinateLenU64 c) in 
    let h, r, uh, hCube = getHHCube #c a1 in 
    let u1, u2, s1, s2 = getU1S2 a0 in 
    let  u1_, u2_, s1_, s2_, h_, r_, uh_, hCube_ = getU1HCube a in 
    u1_ == u1 /\ u2_ == u2 /\ s1_ == s1 /\ s2_ == s2 /\ h_ == h /\ r_ == r /\ uh_ == uh /\ 
      hCube_ == hCube)

let l0 #c a h0 p q = l_main #c a h0 

val lemma_disjoint_invariant: #c: curve 
  -> a: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) 
  -> b: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Lemma 
  (requires (disjoint a b))
  (ensures (let len = getCoordinateLenU64 c in 
    let t4 = gsub a (size 8 *! len) (size 4 *! len) in 
    let h, r, uh, hCube = getHHCube #c t4 in 
    disjoint hCube b /\ disjoint uh b /\ disjoint r b /\ disjoint b h))


let lemma_disjoint_invariant #c a b =
  let len = getCoordinateLenU64 c in 

  let t4 = gsub a (size 8 *! len) (size 4 *! len) in 
  let h = gsub t4 (size 0) len in 

  let h = gsub t4 (size 0) len in 
  let r = gsub t4 len len in 
  let uh = gsub t4 (size 2 *! len) len in 
  let hCube = gsub t4 (size 3 *! len) len in 

  assert(disjoint hCube b /\ disjoint uh b /\ disjoint r b /\ disjoint b h)
