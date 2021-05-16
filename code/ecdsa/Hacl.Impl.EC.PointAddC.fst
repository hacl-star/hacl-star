module Hacl.Impl.EC.PointAddC

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open Hacl.Impl.EC.Masking
open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.LowLevel.RawCmp

open Hacl.Impl.EC.PointDouble
open Hacl.Impl.EC.PointAdd


open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul


(* val lemma_norm: #c: curve -> p: point_nat_prime #c {~ (isPointAtInfinity p)} 
  -> q: point_nat_prime #c {~ (isPointAtInfinity q)} ->  Lemma (
  let pX, pY, pZ = p in
  let qX, qY, qZ = q in 
  let pNX, pNY, pNZ = _norm p in 
  let qNX, qNY, qNZ = _norm q in 
  (pX == qX <==> pNX * (pZ * pZ) % getPrime c == qNX * (qZ * qZ) % getPrime c) /\ 
  (pY == qY <==> pNY * (pZ * pZ * pZ) % getPrime c == qNY * (qZ * qZ * qZ) % getPrime c))


Hacl.Spec.MontgomeryMultiplication
 *)



(* 
The formulas for complete point addition for jacobian coordinates require a check for points not to be 
equal to each other. See more in : 

Weierstraß Elliptic Curves and Side-Channel Attacks Eric Brier and Marc Joye. 

Such way we don't provide a method to compute it, but the following code is used as a wrapper over the check of point equality,
followed by point double (if they are equal) or point add (otherwise).


 *)


val point_add_c: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
   Stack unit (requires fun h -> 
     live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
     
     eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
     disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\ 
     
     point_eval c h p /\ point_eval c h q
   )
   (ensures fun h0 _ h1 -> 
     modifies (loc tempBuffer |+| loc result) h0 h1)


let point_add_c #c p q result tempBuffer = 
  let len = getCoordinateLenU64 c in 
  
  let sq_z1 = sub tempBuffer (size 0) len in 
  let tr_z1 = sub tempBuffer len len in 
  
  let sq_z2 = sub tempBuffer (size 2 *. len) len in 
  let tr_z2 = sub tempBuffer (size 3 *. len) len in 

  let x1 = sub p (size 0) len in 
  let y1 = sub p len len in 
  let z1 = sub p (size 2 *. len) in 

  let x2 = sub q (size 0) len in 
  let y2 = sub q len len in 
  let z2 = sub q (size 2 *. len) in 

  montgomery_square_buffer #c z1 sq_z1;
  montgomery_square_buffer #c z2 sq_z2;

  montgomery_multiplication_buffer #c sq_z1 z1 tr_z1;
  montgomery_multiplication_buffer #c sq_z2 z2 tr_z2;

  montgomery_multiplication_buffer #c sq_z1 x2 sq_z1;
  montgomery_multiplication_buffer #c sq_z2 x1 sq_z2;

  montgomery_multiplication_buffer #c tr_z1 y2 tr_z1;
  montgomery_multiplication_buffer #c tr_z2 y1 tr_z2;

  let equalX = cmp_felem_felem_u64 #c sq_z1 sq_z2 in 
  let equalY = cmp_felem_felem_u64 #c tr_z1 tr_z2 in 

  let equalXandY = equalX && equalY in 

  if equalXandY then
   point_double p result tempBuffer
  else  
    point_add p q result tempBuffer
(* 


prime = 2^256 - 2^224 + 2^ 192 + 2^ 96 -1

x1 = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
y1 = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
z1 = 1

r = 3
x2 = r * r * x1
y2 = r * r * r * y1
z2 = z1 * r

print(x1 * z2 * z2 % prime == x2 * z1 * z1 % prime)

 
def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

print(norm((x1, y1, z1)))
print(norm((x2, y2, z2))) *)
