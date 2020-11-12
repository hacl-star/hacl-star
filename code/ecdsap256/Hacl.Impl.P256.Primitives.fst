module Hacl.Impl.P256.Primitives

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Spec.ECDSA
open Spec.P256.Definitions
open Spec.DH
open Spec.ECDSAP256.Definition
open Spec.P256.Lemmas

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Signature.Common

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


inline_for_extraction noextract
val secretToPublic:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)

let secretToPublic result scalar = 
    push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in
  let resultBufferX = sub resultBuffer (size 0) (size 4) in
  let resultBufferY = sub resultBuffer (size 4) (size 4) in
  let resultX = sub result (size 0) (size 32) in
  let resultY = sub result (size 32) (size 32) in

  secretToPublic resultBuffer scalar tempBuffer;
  let flag = isPointAtInfinityPrivate resultBuffer in

  let h0 = ST.get() in
  changeEndian resultBufferX;
  changeEndian resultBufferY;

  toUint8 resultBufferX resultX;
  toUint8 resultBufferY resultY;

  lemma_core_0 resultBufferX h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferX);
  changeEndian_le_be (as_nat h0 resultBufferX);

  lemma_core_0 resultBufferY h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferY);
  changeEndian_le_be (as_nat h0 resultBufferY); 
  pop_frame();

  let open Hacl.Impl.P256.LowLevel.RawCmp in 
  unsafe_bool_of_u64  flag



(*
  This function provides a raw implementation of the secrettopublic function. 
  It doesnot provide the verification that the point gotten at the result doesnot belong to infinity.
  We strongly encourage you to use this function only if you understand what you´re doing.
*)

inline_for_extraction noextract
val secretToPublicRaw:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack unit
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)


let secretToPublicRaw result scalar =
  push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in
  let resultBufferX = sub resultBuffer (size 0) (size 4) in
  let resultBufferY = sub resultBuffer (size 4) (size 4) in
  let resultX = sub result (size 0) (size 32) in
  let resultY = sub result (size 32) (size 32) in

  Hacl.Impl.P256.Core.secretToPublic resultBuffer scalar tempBuffer;
  let h0 = ST.get() in
  changeEndian resultBufferX;
  changeEndian resultBufferY;

  toUint8 resultBufferX resultX;
  toUint8 resultBufferY resultY;

  lemma_core_0 resultBufferX h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferX);
  changeEndian_le_be (as_nat h0 resultBufferX);

  lemma_core_0 resultBufferY h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 resultBufferY);
  changeEndian_le_be (as_nat h0 resultBufferY); 
  pop_frame();
  admit()


val _scalarMult:
    result:lbuffer uint64 (size 12) 
  -> pubKey:lbuffer uint64 (size 8) 
  -> scalar: lbuffer uint8 (size 32) 
  -> Stack uint64
    (requires fun h -> 
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar /\
      as_nat h (gsub result (size 0) (size 4)) == 0 /\
      as_nat h (gsub result (size 4) (size 4)) == 0)
    (ensures fun h0 r h1 -> 
      modifies (loc result) h0 h1 /\
      (let x, y = as_nat h0 (gsub pubKey (size 0) (size 4)), as_nat h0 (gsub pubKey (size 4) (size 4)) in
       let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
       let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
       if not (verifyQValidCurvePointSpec (pointJacX, pointJacY, pointJacZ)) then
         uint_v r = maxint U64 /\ x3 == 0 /\ y3 == 0
       else
        x3 < prime256 /\ y3 < prime256 /\ z3 < prime256 /\
        (let xN, yN, zN = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in
         xN == x3 /\ yN == y3 /\ zN == z3 /\
         (if isPointAtInfinity (xN, yN, zN) then
           uint_v r = maxint U64
         else
           uint_v r = 0))))


let _scalarMult result pubKey scalar =
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



val _scalarMultRaw:
    result:lbuffer uint64 (size 12) 
  -> pubKey:lbuffer uint64 (size 8) 
  -> scalar: lbuffer uint8 (size 32) 
  -> Stack unit (requires fun h -> 
    live h result /\ live h pubKey /\ live h scalar /\
    disjoint result pubKey /\ disjoint result scalar /\
    as_nat h (gsub result (size 0) (size 4)) == 0 /\
    as_nat h (gsub result (size 4) (size 4)) == 0 /\ (
    let x, y = as_nat h (gsub pubKey (size 0) (size 4)), as_nat h (gsub pubKey (size 4) (size 4)) in 
    x < prime256 /\ y < prime256))
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let x, y = as_nat h0 (gsub pubKey (size 0) (size 4)), as_nat h0 (gsub pubKey (size 4) (size 4)) in
    let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in
    x3 < prime256 /\ y3 < prime256 /\ z3 < prime256 /\
    (let xN, yN, zN = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ) in
    xN == x3 /\ yN == y3 /\ zN == z3)))


let _scalarMultRaw result pubKey scalar =
  push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let publicKeyBuffer = create (size 12) (u64 0) in
  bufferToJac pubKey publicKeyBuffer;
  scalarMultiplication publicKeyBuffer result scalar tempBuffer;
  pop_frame();
  admit()


inline_for_extraction noextract
val scalarMult:
    result:lbuffer uint8 (size 64)
  -> pubKey:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 32) in
      let pubKeyY = gsub pubKey (size 32) (size 32) in
      let pointX, pointY, flag =
        ecp256_dh_r (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub result (size 32) (size 32)) == pointY)


let scalarMult result pubKey scalar =
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

  toUint64ChangeEndian pubKeyX publicKeyFelemX;
  toUint64ChangeEndian pubKeyY publicKeyFelemY;

  let h1 = ST.get() in
  lemma_core_0 publicKeyFelemX h1;
  changeEndianLemma (uints_from_bytes_be (as_seq h0 pubKeyX));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyX);

  lemma_core_0 publicKeyFelemY h1;
  changeEndianLemma (uints_from_bytes_be (as_seq h0 pubKeyY));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyY);

  let flag = _scalarMult resultBufferFelem publicKeyAsFelem scalar in

  let h2 = ST.get() in
  
  changeEndian resultBufferFelemX;
  changeEndian resultBufferFelemY;
  toUint8 resultBufferFelemX resultX;
  toUint8 resultBufferFelemY resultY;

  lemma_core_0 resultBufferFelemX h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemX);
  changeEndian_le_be (as_nat h2 resultBufferFelemX);

  lemma_core_0 resultBufferFelemY h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemY);
  changeEndian_le_be (as_nat h2 resultBufferFelemY);

  pop_frame();
  
  let open Hacl.Impl.P256.LowLevel.RawCmp in 
  unsafe_bool_of_u64  flag




inline_for_extraction noextract
val scalarMultRaw:
    result:lbuffer uint8 (size 64)
  -> pubKey:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack unit
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar /\ (
      let x, y = gsub pubKey (size 0) (size 32), gsub pubKey (size 32) (size 32) in 
      nat_from_bytes_be (as_seq h x) < prime /\
      nat_from_bytes_be (as_seq h y) < prime))
    (ensures fun h0 _ h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 32) in
      let pubKeyY = gsub pubKey (size 32) (size 32) in
      let pointX, pointY, flag =
        ecp256_dh_r (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub result (size 32) (size 32)) == pointY)


let scalarMultRaw result pubKey scalar =
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

  toUint64ChangeEndian pubKeyX publicKeyFelemX;
  toUint64ChangeEndian pubKeyY publicKeyFelemY;

  let h1 = ST.get() in
  lemma_core_0 publicKeyFelemX h1;
  changeEndianLemma (uints_from_bytes_be (as_seq h0 pubKeyX));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyX);

  lemma_core_0 publicKeyFelemY h1;
  changeEndianLemma (uints_from_bytes_be (as_seq h0 pubKeyY));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 pubKeyY);

  _scalarMult resultBufferFelem publicKeyAsFelem scalar;

  let h2 = ST.get() in
  
  changeEndian resultBufferFelemX;
  changeEndian resultBufferFelemY;
  toUint8 resultBufferFelemX resultX;
  toUint8 resultBufferFelemY resultY;

  lemma_core_0 resultBufferFelemX h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemX);
  changeEndian_le_be (as_nat h2 resultBufferFelemX);

  lemma_core_0 resultBufferFelemY h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 resultBufferFelemY);
  changeEndian_le_be (as_nat h2 resultBufferFelemY);

  pop_frame();
  admit()


val _toForm: i:lbuffer uint8 (size 32) -> o:felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 ->
    modifies (loc o) h0 h1 /\
    as_seq h1 o == Spec.ECDSA.changeEndian (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i))
  )

let _toForm i o = toUint64ChangeEndian i o


val toFormPoint: i: lbuffer uint8 (size 64) -> p: point -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let toFormPoint i p = 
  let pointScalarX = sub i (size 0) (size 32) in 
  let pointScalarY = sub i (size 32) (size 32) in 

  let pointX = sub p (size 0) (size 4) in 
  let pointY = sub p (size 4) (size 4) in 
  let pointZ = sub p (size 8) (size 4) in 

  _toForm pointScalarX pointX;
  _toForm pointScalarY pointY;
  uploadOneImpl pointZ


val _fromForm: i: felem -> o: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let _fromForm i o = 
  changeEndian i;
  toUint8 i o


val fromFormPoint: i: point -> o: lbuffer uint8 (size 64) -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let fromFormPoint i o = 
  let pointX = sub i (size 0) (size 4) in 
  let pointY = sub i (size 4) (size 4) in 

  let pointScalarX = sub i (size 0) (size 32) in 
  let pointScalarY = sub i (size 32) (size 32) in 

  _fromForm pointX pointScalarX;
  _fromForm pointY pointScalarY
