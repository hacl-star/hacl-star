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
val _toForm: i:lbuffer uint8 (size 32) -> o:felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 ->
    modifies (loc o) h0 h1 /\ as_nat h1 o == nat_from_bytes_be (as_seq h0 i))

let _toForm i o = 
    let h0 = ST.get() in 
  toUint64ChangeEndian i o;
    let h1 = ST.get() in 
  changeEndianLemma (uints_from_bytes_be (as_seq h0 i));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 i);
  lemma_core_0 o h1


val toFormPoint: i: lbuffer uint8 (size 64) -> result: point -> Stack unit 
  (requires fun h -> live h i /\ live h result /\ disjoint i result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h0 (gsub i (size 0) (size 32))) in 
    let pointScalarYSeq = nat_from_bytes_be (as_seq h0 (gsub i (size 32) (size 32))) in 
    let x, y, z = point_prime_to_coordinates (as_seq h1 result) in 
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (pointScalarXSeq, pointScalarYSeq) in 
    x == pointScalarXSeq /\ y == pointScalarYSeq /\ z == 1 /\
    x == pointJacX /\ y == pointJacY /\ z == pointJacZ))

      
let toFormPoint i p = 
  let pointScalarX = sub i (size 0) (size 32) in 
  let pointScalarY = sub i (size 32) (size 32) in 

  let pointX = sub p (size 0) (size 4) in 
  let pointY = sub p (size 4) (size 4) in 
  let pointZ = sub p (size 8) (size 4) in 

  _toForm pointScalarX pointX;
  _toForm pointScalarY pointY;
  uploadOneImpl pointZ


inline_for_extraction noextract
val _fromForm: i: felem -> o: lbuffer uint8 (size 32) -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ as_nat h i < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\  as_seq h1 o == nat_to_bytes_be 32  (as_nat h0 i))

let _fromForm i o = 
    let h0 = ST.get() in 
  changeEndian i;
  toUint8 i o;
  
  lemma_core_0 i h0;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h0 i);
  changeEndian_le_be (as_nat h0 i)


val fromFormPoint: i: point -> o: lbuffer uint8 (size 64) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\
    as_nat h (gsub i (size 0) (size 4)) < prime256 /\
    as_nat h (gsub i (size 4) (size 4)) < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\ (
    let xCoordinate = gsub i (size 0) (size 4) in 
    let yCoordinate = gsub i (size 4) (size 4) in 

    let scalarX = gsub o (size 0) (size 32) in 
    let scalarY = gsub o (size 32) (size 32) in 

    as_seq h1 scalarX == nat_to_bytes_be 32 (as_nat h0 xCoordinate) /\
    as_seq h1 scalarY == nat_to_bytes_be 32 (as_nat h0 yCoordinate)))


let fromFormPoint i o = 
  let pointX = sub i (size 0) (size 4) in 
  let pointY = sub i (size 4) (size 4) in 

  let pointScalarX = sub o (size 0) (size 32) in 
  let pointScalarY = sub o (size 32) (size 32) in 

  _fromForm pointX pointScalarX;
  _fromForm pointY pointScalarY




inline_for_extraction noextract
val secretToPublic:
  m: montgomery_ladder_mode
  -> result:lbuffer uint8 (size 64)
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
    

let secretToPublic m result scalar = 
    push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in
  
  secretToPublic m resultBuffer scalar tempBuffer;
  let flag = isPointAtInfinityPrivate resultBuffer in
  fromFormPoint resultBuffer result;
  
  pop_frame();

  let open Hacl.Impl.P256.LowLevel.RawCmp in 
  unsafe_bool_of_u64  flag


(*
  This function provides a raw implementation of the secrettopublic function. 
  It doesnot provide the verification that the point gotten at the result doesnot belong to infinity.
  We strongly discourage you to use this function unless you understand what you´re doing.
  A. 
*)

inline_for_extraction noextract
val secretToPublicRaw:
  m: montgomery_ladder_mode
  ->  result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack unit
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    modifies (loc result) h0 h1 /\ (
    let (xN, yN, zN) = secret_to_public (as_seq h0 scalar)  in 

    let scalarX = gsub result (size 0) (size 32) in 
    let scalarY = gsub result (size 32) (size 32) in 

    as_seq h1 scalarX == nat_to_bytes_be 32 xN /\
    as_seq h1 scalarY == nat_to_bytes_be 32 yN))


let secretToPublicRaw m result scalar =
  push_frame();
  let tempBuffer = create (size 100) (u64 0) in
  let resultBuffer = create (size 12) (u64 0) in

  Hacl.Impl.P256.Core.secretToPublic m resultBuffer scalar tempBuffer;  
  fromFormPoint resultBuffer result;
  pop_frame()


inline_for_extraction noextract
val scalarMult:
  m: montgomery_ladder_mode
  -> result:lbuffer uint8 (size 64)
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


let scalarMult m result pubKey scalar =
  push_frame();
  
  let resultBufferFelem = create (size 12) (u64 0) in
  let publicKeyAsFelem = create (size 12) (u64 0) in
  let tempBuffer = create (size 100) (u64 0) in
  
  toFormPoint pubKey publicKeyAsFelem; 
  let publicKeyCorrect = verifyQValidCurvePoint publicKeyAsFelem tempBuffer in
  
  let flag = 
    if publicKeyCorrect then
      begin
      scalarMultiplication m publicKeyAsFelem resultBufferFelem scalar tempBuffer;
      isPointAtInfinityPrivate resultBufferFelem 
      end
    else 
      u64 18446744073709551615 in 
      
  (* This line is a bit suspicious *)
  fromFormPoint resultBufferFelem result;
  
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
      nat_from_bytes_be (as_seq h x) < prime256 /\
      nat_from_bytes_be (as_seq h y) < prime256))
    (ensures fun h0 _ h1 -> modifies (loc result |+| loc pubKey) h0 h1 /\ (
      let pointScalarXSeq = nat_from_bytes_be (as_seq h0 (gsub pubKey (size 0) (size 32))) in 
      let pointScalarYSeq = nat_from_bytes_be (as_seq h0 (gsub pubKey (size 32) (size 32))) in  
      let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (pointScalarXSeq, pointScalarYSeq) in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (pointJacX, pointJacY, pointJacZ ) in 
      let scalarX = gsub result (size 0) (size 32) in 
      let scalarY = gsub result (size 32) (size 32) in 
  
      as_seq h1 scalarX == nat_to_bytes_be 32 xN /\
      as_seq h1 scalarY == nat_to_bytes_be 32 yN
    )
  )

let scalarMultRaw result pubKey scalar =
  push_frame();
  
  let resultBufferFelem = create (size 12) (u64 0) in
  let publicKeyAsFelem = create (size 12) (u64 0) in
  let tempBuffer = create (size 100) (u64 0) in
    
  toFormPoint pubKey publicKeyAsFelem; 
  (* with normalisation *)
  scalarMultiplication Radix4 publicKeyAsFelem resultBufferFelem scalar tempBuffer;
  fromFormPoint resultBufferFelem result;

  pop_frame()


inline_for_extraction noextract
val ecdsa_verification_point_operations: result: lbuffer uint8 (size 32) -> publicKey: lbuffer uint8 (size 64) -> 
  u1: lbuffer uint8 (size 32) -> u2: lbuffer uint8 (size 32) ->
  Stack bool 
  (requires fun h -> live h result /\ live h publicKey /\ live h u1 /\ live h u2 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc publicKey; loc u1; loc u2] /\ (
    let publicKeyX = nat_from_bytes_be (as_seq h (gsub publicKey (size 0) (size 32))) in
    let publicKeyY = nat_from_bytes_be (as_seq h (gsub publicKey (size 32) (size 32))) in 
    publicKeyX < prime256 /\ publicKeyY < prime256 ))
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h0 (gsub publicKey (size 0) (size 32))) in 
    let pointScalarYSeq = nat_from_bytes_be (as_seq h0 (gsub publicKey (size 32) (size 32))) in 
    let pubJac = toJacobianCoordinates (pointScalarXSeq, pointScalarYSeq) in 
    let pointAtInfinity = (0, 0, 0) in
    let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in
    let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, pubJac) in
    let sumD = if  _norm u1D =  _norm u2D then  _point_double u1D else  _point_add u1D u2D in 
    let pointNorm = _norm sumD in
    let (xResult, yResult, zResult) = pointNorm in
    r == not (Spec.P256.isPointAtInfinity pointNorm) /\
    as_seq h1 result == nat_to_bytes_be 32  (xResult % prime_p256_order)))


let ecdsa_verification_point_operations result publicKey u1 u2 = 
  push_frame();
    let tempBuffer = create (size 100) (u64 0) in  
    let publicKeyAsFelem = create (size 12) (u64 0) in 
    let resultFelem = create (size 4) (u64 0) in 

  toFormPoint publicKey publicKeyAsFelem;
  let r = Hacl.Impl.ECDSA.P256.Verification.Agile.ecdsa_verification_step5 resultFelem publicKeyAsFelem u1 u2 tempBuffer in 
  _fromForm resultFelem result;
  
  pop_frame();
  r