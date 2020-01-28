module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2

open Hacl.Spec.P256
open Hacl.Spec.ECDSA
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256
open Hacl.Impl.P256.Signature.Common


#reset-options "--z3rlimit 300" 

let ecp256dh_i result scalar = 
  push_frame();
    let tempBuffer = create (size 100) (u64 0) in 
    let resultBuffer = create (size 12) (u64 0) in
    let resultBufferX = sub resultBuffer (size 0) (size 4) in 
    let resultBufferY = sub resultBuffer (size 4) (size 4) in 
    
    let resultX = sub result (size 0) (size 32) in 
    let resultY = sub result (size 32) (size 32) in 

    secretToPublic resultBuffer scalar tempBuffer; 
    let flag = isPointAtInfinityPrivate resultBuffer in 
  let h2 = ST.get() in
    toUint8 resultBufferX resultX;
      lemma_core_1 resultBufferX h2;
      lemma_core_1 resultBufferY h2;
    toUint8 resultBufferY resultY;
  pop_frame(); 
    flag


val _ecp256dh_r: result: lbuffer uint64 (size 12) -> pubKey: lbuffer uint64 (size 8) -> scalar: lbuffer uint8 (size 32) -> 
  Stack uint64 
    (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ 
      disjoint result pubKey /\ disjoint result scalar /\ disjoint pubKey scalar /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) >= 1 /\
      Lib.ByteSequence.nat_from_bytes_le (as_seq h scalar) < Hacl.Spec.ECDSAP256.Definition.prime_p256_order
    )
    (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\
      (
	let x, y = as_nat h0 (gsub pubKey (size 0) (size 4)), as_nat h0 (gsub pubKey (size 4) (size 4)) in 
	let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
	let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in 
	if not (verifyQValidCurvePointSpec (pointJacX, pointJacY, pointJacZ)) then 
	  uint_v r = maxint U64
	else 
	  let xN, yN, zN = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in 
	  xN == x3 /\ yN == y3 /\ zN == z3 /\
	  (
	    if isPointAtInfinity (xN, yN, zN) then 
	      uint_v r = maxint U64
	    else 
	      uint_v r = 0
	  )
      )
  )

let _ecp256dh_r result pubKey scalar = 
  push_frame();
    let h0 = ST.get() in 
    let tempBuffer = create (size 100) (u64 0) in 
    let publicKeyBuffer = create (size 12) (u64 0) in 
    bufferToJac pubKey publicKeyBuffer;
    let publicKeyCorrect = verifyQValidCurvePoint publicKeyBuffer tempBuffer in 
    if publicKeyCorrect = false then 
      begin 
	pop_frame();
	u64 18446744073709551615
      end
    else
      begin
       scalarMultiplication publicKeyBuffer result scalar tempBuffer;
       let flag = isPointAtInfinityPrivate result in 
       pop_frame();
       flag
      end


let ecp256dh_r result pubKey scalar = 
  push_frame(); 
    let h0 = ST.get() in 
      let resultBufferFelem = create (size 12) (u64 0) in 
	let resultBufferFelemX = sub resultBufferFelem (size 0) (size 4) in 
	let resultBufferFelemY = sub resultBufferFelem (size 4) (size 4) in 
	let resultX = sub result (size 0) (size 32) in 
	let resultY = sub result (size 32) (size 32) in 
      
      let publicKeyAsFelem = create (size 8) (u64 0) in 
	let publicKeyFelemX = sub publicKeyAsFelem (size 0) (size 4) in 
	let publicKeyFelemY = sub publicKeyAsFelem (size 4) (size 4) in 
	let pubKeyX = sub pubKey (size 0) (size 32) in 
	let pubKeyY = sub pubKey (size 32) (size 32) in 

      toUint64 pubKeyX publicKeyFelemX;
      toUint64 pubKeyY publicKeyFelemY;
      
      let h1 = ST.get() in 
	lemma_core_0 publicKeyFelemX h1;
	Lib.ByteSequence.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);
	lemma_core_0 publicKeyFelemY h1;
	Lib.ByteSequence.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY); 
	
	let flag = _ecp256dh_r resultBufferFelem publicKeyAsFelem scalar in 
      let h2 = ST.get() in 	
      toUint8 resultBufferFelemX resultX;
	lemma_core_1 resultBufferFelemX h2;
      toUint8 resultBufferFelemY resultY;
	lemma_core_1 resultBufferFelemY h2;
      pop_frame();
      flag
      
