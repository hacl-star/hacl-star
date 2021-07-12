module Spec.ECC

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

open Lib.LoopCombinators 

open FStar.Math.Lemmas
open FStar.Math.Lib

open Spec.ECC.Curves

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


let pointAtInfinity #c : point_nat_prime #c  = (0, 0, 0)

let isPointAtInfinity (p:point_nat) =
  let (_, _, z) = p in z = 0

let isPointAtInfinityAffine (p:point_affine_nat) =
  let (x, y) = p in x = 0 && y = 0


noextract
let _point_double_nist #curve (p:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let x, y, z = p in
  let delta = z * z in 
  let gamma = y * y in 
  let beta = x * gamma in 
  let alpha = 3 * (x - delta) * (x + delta) in 
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha * (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = ((y + z) * (y + z) - delta - gamma) % prime in 
  (x3, y3, z3)


(* https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-1998-cmo-2 *)

noextract
let _point_double_general #curve (p: point_nat_prime #curve) : point_nat_prime #curve = 
  let prime = getPrime curve in 
  let x, y, z = p in
  let gamma = y * y in 
  let delta = z * z in 
  let beta = x * gamma in 
   
  let alpha = 3 * x * x + aCoordinate #curve * delta * delta in 
  
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha * (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = ((y + z) * (y + z) - delta - gamma) % prime in 
  (x3, y3, z3)


noextract
let _point_double_koblitz #curve (p: point_nat_prime #curve) : point_nat_prime #curve = 
  let prime = getPrime curve in 
  let x, y, z = p in
  let gamma = y * y in 
  let delta = z * z in 
  let beta = x * gamma in 
   
  let alpha = 3 * x * x in 
  
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha * (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = ((y + z) * (y + z) - delta - gamma) % prime in 
  (x3, y3, z3)


noextract
let _point_double #curve (p: point_nat_prime) : point_nat_prime #curve = 
  match curve with 
  |P256 -> _point_double_nist p 
  |P384 -> _point_double_nist p
  |Default -> _point_double_general p



 let _norm #curve (p:point_nat_prime #curve) : (point_nat_prime #curve) =
  let prime = getPrime curve in 
  let (x, y, z) = p in
  let z2 = z * z in
  let z2i = modp_inv2 #curve z2 in
  let z3 = z * z * z in
  let z3i = modp_inv2 #curve z3 in
  let x3 = (z2i * x) % prime in
  let y3 = (z3i * y) % prime in
  let z3 = if isPointAtInfinity p then 0 else 1 in
  (x3, y3, z3)


let scalar_bytes (#c: curve) = lbytes (v (getScalarLenBytes c))

let ith_bit (#c: curve) (k: scalar_bytes #c) (i:nat{i < v (getScalarLen c)}) : (r: uint64 {v r == 0 \/ v r == 1}) =
  let q = (v (getScalarLenBytes c) - 1) - i / 8 in 
  let r = size (i % 8) in
  logand_mask (index k q >>. r) (u8 1) 1;
  to_u64 ((index k q >>. r) &. u8 1)
  
let isPointOnCurve (#c: curve) (p: point_nat_prime #c) : bool = 
  let (x, y, z) = p in
  let prime = getPrime c in 
  (y * y) % prime = (x * x * x + aCoordinate #c  * x + bCoordinate #c) % prime


val toJacobianCoordinates: tuple2 nat nat -> r: tuple3 nat nat nat {~ (isPointAtInfinity r)}

let toJacobianCoordinates (r0, r1) = (r0, r1, 1)


let pointEqual #curve (p: point_nat_prime #curve) (q: point_nat_prime #curve) = 
  let pAffineX, pAffineY, pAffineZ = _norm p in 
  let qAffineX, qAffineY, qAffineZ = _norm q in 

  (* if one point is at infinity, but not the second *)
  if pAffineZ <> qAffineZ then false else
  (* if two points are at infinity *)
  if pAffineZ = 0 && qAffineZ = 0 then true else
  (* if affine coordinates are equal *)
  if (pAffineX = qAffineX && pAffineY = qAffineY) then 
    true
  else false



noextract
let _point_add #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 * z2 in
  let z1z1 = z1 * z1 in

  let u1 = x1 * z2z2 % prime in
  let u2 = x2 * z1z1 % prime in

  let s1 = y1 * z2 * z2z2 % prime in
  let s2 = y2 * z1 * z1z1 % prime in

  let h = (u2 - u1) % prime in
  let r = (s2 - s1) % prime in

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3 = (rr - hhh - 2 * u1 * hh) % prime in
  let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime in
  let z3 = (h * z1 * z2) % prime in
  if z2 = 0 then
    (x1, y1, z1)
  else
    if z1 = 0 then
      (x2, y2, z2)
    else
      (x3, y3, z3)


noextract
let _point_add_mixed #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 * z2 in
  let z1z1 = z1 * z1 in

  let u1 = x1 * z2z2 % prime in
  let u2 = x2 * z1z1 % prime in

  let s1 = y1 * z2 * z2z2 % prime in
  let s2 = y2 * z1 * z1z1 % prime in

  let h = (u2 - u1) % prime in
  let r = (s2 - s1) % prime in

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3 = (rr - hhh - 2 * u1 * hh) % prime in
  let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime in
  let z3 = (h * z1 * z2) % prime in
  if isPointAtInfinityAffine (x2, y2) then
    (x1, y1, z1)
  else
    if z1 = 0 then
      (x2, y2, z2)
    else
      (x3, y3, z3)



let pointAdd #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  if pointEqual p q then 
    _point_double p 
  else
    _point_add p q


let point_mult #c i (p: point_nat_prime #c) : point_nat_prime #c  = repeat ((i - 1) % getOrder #c) (fun x -> pointAdd #c p x) p
