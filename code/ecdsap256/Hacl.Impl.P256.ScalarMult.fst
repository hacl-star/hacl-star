module Hacl.Impl.P256.ScalarMult

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Spec.ECDSA
open Spec.P256.Definitions
open Hacl.Spec.P256.Felem
open Spec.DH
open Spec.ECDSAP256.Definition
open Spec.P256.Lemmas

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Signature.Common
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.LowLevel.RawCmp


#set-options " --z3rlimit 200 --ifuel 0 --fuel 0"

val isCoordinateValidPrivate: p: point -> Stack uint64
  (requires fun h -> live h p /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    v r == pow2 64 - 1 <==> (point_x_as_nat h0 p < prime256 && point_y_as_nat h0 p < prime256 && point_z_as_nat h0 p < prime256))

let isCoordinateValidPrivate p = 
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in 
  recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
  let x = sub p (size 0) (size 4) in 
  let y = sub p (size 4) (size 4) in 
  
  let carryX = sub4_il x prime256_buffer tempBuffer in
  let carryY = sub4_il y prime256_buffer tempBuffer in 
  
  let lessX = eq_mask carryX (u64 1) in   
    eq_mask_lemma carryX (u64 1);
    eq_mask_lemma carryY (u64 1);
  let lessY = eq_mask carryY (u64 1) in 
  let r = logand lessX lessY in 
    logand_lemma lessX lessY;
  pop_frame();
  r  




(*

[@ (Comment "  The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.")] 
val _ecp256scalar_mult:
    result:lbuffer uint64 (size 12) 
  -> pubKey:lbuffer uint64 (size 8) 
  -> scalar: lbuffer uint8 (size 32) 
  -> Stack uint64
  (requires fun h -> 
    live h result /\ live h pubKey /\ live h scalar /\
    disjoint result pubKey /\ disjoint result scalar /\
    as_nat h (gsub result (size 0) (size 4)) == 0 /\
    as_nat h (gsub result (size 4) (size 4)) == 0)
  (ensures fun h0 r h1 ->  modifies (loc result) h0 h1 /\ (
    let x, y = as_nat h0 (gsub pubKey (size 0) (size 4)), as_nat h0 (gsub pubKey (size 4) (size 4)) in
    let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
    if not (verifyQValidCurvePointSpec (pointJacX, pointJacY, pointJacZ)) then
      uint_v r = maxint U64 /\ x3 == 0 /\ y3 == 0
    else
      x3 < prime256 /\ y3 < prime256 /\ z3 < prime256 /\ (
      let xN, yN, zN = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in
      xN == x3 /\ yN == y3 /\ zN == z3 /\ (
      if isPointAtInfinity (xN, yN, zN) then
	uint_v r = maxint U64
      else
	uint_v r = 0))))


let _ecp256scalar_mult result pubKey scalar =
  push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let publicKeyBuffer = create (size 12) (u64 0) in
  bufferToJac pubKey publicKeyBuffer;
  let publicKeyCorrect = verifyQValidCurvePoint publicKeyBuffer tempBuffer in
  if publicKeyCorrect then
    begin
    scalarMultiplication publicKeyBuffer result scalar tempBuffer;
    let flag = isPointAtInfinityPrivate result in
    pop_frame();
    flag
    end
  else
    begin
    pop_frame();
    u64 18446744073709551615
    end
