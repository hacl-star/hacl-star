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


#set-options " --z3rlimit 200 --max_fuel 0 --max_ifuel 0"

open FStar.Mul 

val ecp256_dh_i_: #c: curve -> resultBuffer: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) 
  -> scalar: scalar_t #MUT #c -> result: pointAffine8 c -> 
  Stack uint64
  (requires fun h -> live h resultBuffer /\ live h tempBuffer /\ live h scalar /\ live h result /\
    disjoint resultBuffer result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc resultBuffer])
  (ensures fun h0 r h1 -> modifies (loc result |+| loc tempBuffer |+| loc resultBuffer) h0 h1 /\ (
    let pointX, pointY, flag = ecp256_dh_i #c (as_seq h0 scalar) in 
    let coordinateX_u8, coordinateY_u8 = getXAff8 #c result, getYAff8 #c result in
    let scalarX, scalarY = as_seq h1 (coordinateX_u8), as_seq h1 (coordinateY_u8) in 
    pointX == scalarX /\ pointY == scalarY /\ r == flag))


let ecp256_dh_i_ #c resultBuffer tempBuffer scalar result = 
  secretToPublic #c resultBuffer scalar tempBuffer;
    let h1 = ST.get() in 
  let r = isPointAtInfinityPrivate #c resultBuffer in 
    let h2 = ST.get() in 
  fromFormPoint #c resultBuffer result;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 resultBuffer;
  r


let ecp256dh_i c result scalar =
  push_frame();
  let len = getCoordinateLenU64 c in 
  let tempBuffer = create (size 20 *! len) (u64 0) in
  let resultBuffer = create (size 3 *! len) (u64 0) in
    let h0 = ST.get() in 
  let flag = ecp256_dh_i_ resultBuffer tempBuffer scalar result in 
  pop_frame();
  flag


[@ (Comment "  This code is not side channel resistant on pubKey")]
val _ecp256dh_r: #c: curve 
  -> result: point c
  -> pubKey: pointAffine c
  -> scalar: scalar_t #MUT #c -> 
  Stack uint64
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ 
    disjoint result pubKey /\ disjoint result scalar /\
    felem_eval c h (getXAff pubKey) /\ felem_eval c h (getYAff pubKey) /\
    as_nat c h (getX result) == 0 /\ as_nat c h (getY result) == 0 /\ as_nat c h (getZ result) == 0)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
    let pkX, pkY = as_nat c h0 (getXAff pubKey), as_nat c h0 (getYAff pubKey) in 
    let x3, y3, z3 = point_as_nat c h1 result in
    let pointJ = toJacobianCoordinates (pkX, pkY) in 
    if not (verifyQValidCurvePointSpec #c pointJ) then
      uint_v r = maxint U64 /\ x3 == 0 /\ y3 == 0
    else begin
      let xN, yN, zN = scalar_multiplication #c (as_seq h0 scalar) pointJ in
      xN == x3 /\ yN == y3 /\ zN == z3 /\ (
      if isPointAtInfinity (xN, yN, zN) then
	uint_v r = maxint U64
      else
	uint_v r = 0) end))


let _ecp256dh_r #c result pubKey scalar =
    let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 20 *! len) (u64 0) in
    let publicKeyBuffer = create (size 3 *! len) (u64 0) in
  bufferToJac #c pubKey publicKeyBuffer; 
    let h1 = ST.get() in 

  let publicKeyCorrect = verifyQValidCurvePoint #c publicKeyBuffer tempBuffer in 
  if publicKeyCorrect then
    begin
        let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 publicKeyBuffer;
      scalarMultiplication #c #MUT publicKeyBuffer result scalar tempBuffer;
	let h3 = ST.get() in 
      let flag = isPointAtInfinityPrivate #c result in
	pop_frame();
	let h4 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 result;
      flag
    end
  else
    begin
      pop_frame();
	let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
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
