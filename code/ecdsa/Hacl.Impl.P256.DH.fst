module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECC
open Spec.ECDSA
open Hacl.Spec.EC.Definition
open Spec.DH
open Hacl.Spec.ECDSA.Definition
open Hacl.Lemmas.P256

open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.Core
open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.EC.Intro

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let ecp256dh_i c result scalar =
  push_frame();
  let len = getCoordinateLenU64 c in 
  let scalarLen = getScalarLenBytes c in 

  let tempBuffer = create (size 25 *! len) (u64 0) in
    
  let resultBuffer = create (size 3 *! len) (u64 0) in
  let resultBufferX = sub resultBuffer (size 0) len in
  let resultBufferY = sub resultBuffer len len in
    
  let resultX = sub result (size 0) scalarLen in
  let resultY = sub result scalarLen scalarLen in

  secretToPublic #c resultBuffer scalar tempBuffer;

  let flag = isPointAtInfinityPrivate #c resultBuffer in

  let h0 = ST.get() in
(*   changeEndian #c resultBufferX;
  changeEndian #c resultBufferY;
 *)
  toUint8 #c resultBufferX resultX;
  toUint8 #c resultBufferY resultY;

  lemma_core_0 c resultBufferX h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferX);
  (* changeEndian_le_be #c (as_nat c h0 resultBufferX); *)

  lemma_core_0 c resultBufferY h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferY);
  (* changeEndian_le_be #c (as_nat c h0 resultBufferY);  *)
  pop_frame();
  flag


(*
[@ (Comment "  This code is not side channel resistant on pubKey")]
*)

val _ecp256dh_r:
  #c: curve 
  -> result:lbuffer uint64 (size 3 *! getCoordinateLenU64 c) 
  -> pubKey:lbuffer uint64 (size 2 *! getCoordinateLenU64 c) 
  -> scalar: lbuffer uint8 (getScalarLen c) 
  -> Stack uint64
    (requires fun h -> 
      let len = getCoordinateLenU64 c in 
      
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar /\
      
      as_nat c h (gsub result (size 0) len) == 0 /\
      as_nat c h (gsub result len len) == 0
   )
    (ensures fun h0 r h1 -> 
      let len = getCoordinateLenU64 c in 
      let prime = getPrime c in       
      
      modifies (loc result) h0 h1 /\ (
      
      let x, y = as_nat c h0 (gsub pubKey (size 0) len), as_nat c h0 (gsub pubKey len len) in
      
       let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
       let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
       if not (verifyQValidCurvePointSpec #c (pointJacX, pointJacY, pointJacZ)) then
	 uint_v r = maxint U64 /\ x3 == 0 /\ y3 == 0
       else
	 x3 < prime /\ y3 < prime /\ z3 < prime /\
         (
	   let xN, yN, zN = scalar_multiplication #c (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in
           xN == x3 /\ yN == y3 /\ zN == z3 /\
         (if isPointAtInfinity (xN, yN, zN) then
           uint_v r = maxint U64
         else
           uint_v r = 0))))


let _ecp256dh_r #c result pubKey scalar =
  push_frame();
  admit();
  let len = getCoordinateLenU64 c in 
  let tempBuffer = create (size 25 *! len) (u64 0) in
  let publicKeyBuffer = create (size 3 *! len) (u64 0) in
  bufferToJac #c pubKey publicKeyBuffer;
  let publicKeyCorrect = verifyQValidCurvePoint #c publicKeyBuffer tempBuffer in
  if publicKeyCorrect then
    begin
    scalarMultiplication #c publicKeyBuffer result scalar tempBuffer;
    let flag = isPointAtInfinityPrivate #c result in
    pop_frame();
    flag
    end
  else
    begin
    pop_frame();
    u64 18446744073709551615
    end


let ecp256dh_r c result pubKey scalar =
  push_frame();
  let h0 = ST.get() in
  
  let len = getCoordinateLenU64 c in 

  let resultBufferFelem = create (size 3 *! len) (u64 0) in
  let resultBufferFelemX = sub resultBufferFelem (size 0) len in
  let resultBufferFelemY = sub resultBufferFelem len len in
  let resultX = sub result (size 0) (getScalarLenBytes c) in
  let resultY = sub result (getScalarLenBytes c) (getScalarLenBytes c) in

  let publicKeyAsFelem = create (size 2 *! len) (u64 0) in
  let publicKeyFelemX = sub publicKeyAsFelem (size 0) len in
  let publicKeyFelemY = sub publicKeyAsFelem len len in
  let pubKeyX = sub pubKey (size 0) (getScalarLenBytes c) in
  let pubKeyY = sub pubKey (getScalarLenBytes c) (getScalarLenBytes c) in

  toUint64ChangeEndian #c pubKeyX publicKeyFelemX;
  toUint64ChangeEndian #c pubKeyY publicKeyFelemY;

  let h1 = ST.get() in
  lemma_core_0 c publicKeyFelemX h1;
  (* changeEndianLemma #c (uints_from_bytes_be (as_seq h0 pubKeyX)); *)
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyX);

  lemma_core_0 c publicKeyFelemY h1;
  (* changeEndianLemma #c (uints_from_bytes_be (as_seq h0 pubKeyY)); *)
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyY);

  let flag = _ecp256dh_r #c resultBufferFelem publicKeyAsFelem scalar in

  let h2 = ST.get() in
  
  changeEndian #c resultBufferFelemX;
  changeEndian #c resultBufferFelemY;
  toUint8 #c resultBufferFelemX resultX;
  toUint8 #c resultBufferFelemY resultY;

  lemma_core_0 c resultBufferFelemX h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemX);
  (* changeEndian_le_be #c (as_nat c h2 resultBufferFelemX); *)

  lemma_core_0 c resultBufferFelemY h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemY);
  (* changeEndian_le_be #c (as_nat c h2 resultBufferFelemY); *)

  pop_frame();
  flag
