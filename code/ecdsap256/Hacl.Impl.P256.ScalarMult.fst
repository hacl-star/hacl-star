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

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.Signature.Common
open Hacl.Impl.P256.LowLevel.PrimeSpecific

open FStar.Math.Lemmas

open FStar.Mul

friend Hacl.Impl.P256.Signature.Common


#set-options " --z3rlimit 200 --ifuel 0 --fuel 0"

val isCoordinateValidPrivate: p: point -> Stack uint64
  (requires fun h -> live h p /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (v r = 0 \/ v r == ones_v U64) /\ (
    v r == pow2 64 - 1 <==> (point_x_as_nat h0 p < prime256 && point_y_as_nat h0 p < prime256 && point_z_as_nat h0 p < prime256)))

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


val isPointOnCurvePrivate: p: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack uint64
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer)
  (ensures fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (v r = 0 \/ v r == ones_v U64) /\ (
    let point = as_nat h1 (gsub p (size 0) (size 4)), as_nat h1 (gsub p (size 4) (size 4)), as_nat h1 (gsub p (size 8) (size 4)) in 
    v r == pow2 64 - 1 <==> isPointOnCurve point))

let isPointOnCurvePrivate p tempBuffer = 
  let y2Buffer = sub tempBuffer (size 0) (size 4) in 
  let xBuffer = sub tempBuffer (size 4) (size 4)  in 
  let h0 = ST.get() in 
  let x = sub p (size 0) (size 4) in 
  let y = sub p (size 4) (size 4) in 

  reduction_prime_2prime_impl y y2Buffer;
  reduction_prime_2prime_impl x xBuffer;
  
  y_2 y2Buffer y2Buffer;
  xcube_minus_x xBuffer xBuffer;

  lemma_modular_multiplication_p256_2_d ((as_nat h0 y) * (as_nat h0 y) % prime256) 
    (let x_ = as_nat h0 x in (x_ * x_ * x_ - 3 * x_ + Spec.P256.bCoordinateP256) % prime256);

  let h1 = ST.get() in 
  let r = compare_felem y2Buffer xBuffer in 

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  calc (==) {
    (as_nat h0 y % prime256) * (as_nat h0 y % prime256) % prime256;
    (==) {lemma_mod_mul_distr_l (as_nat h0 y) (as_nat h0 y % prime256) prime256}
    as_nat h0 y * (as_nat h0 y % prime256) % prime256;
    (==) {lemma_mod_mul_distr_r (as_nat h0 y) (as_nat h0 y) prime256}
    as_nat h0 y * as_nat h0 y % prime256;
  };

  calc (==) {
    ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256) - 3 * (as_nat h0 x % prime256) + Spec.P256.bCoordinateP256) % prime256;
    (==) {
      lemma_mod_sub_distr ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256) + Spec.P256.bCoordinateP256) (3 * (as_nat h0 x % prime256)) prime256;
      lemma_mod_mul_distr_r 3 (as_nat h0 x) prime256;
      lemma_mod_sub_distr ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256) + Spec.P256.bCoordinateP256) (3 * (as_nat h0 x)) prime256
    }
    ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256) - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;
    (==) {lemma_mod_add_distr (- (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256)) prime256}
    ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256) % prime256 - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;
    (==) {
      assert_by_tactic ((as_nat h0 x % prime256) * (as_nat h0 x % prime256) * (as_nat h0 x % prime256)  == 
      (as_nat h0 x % prime256) * ((as_nat h0 x % prime256) * (as_nat h0 x % prime256))) canon;
      
      lemma_mod_mul_distr_l (as_nat h0 x) ((as_nat h0 x % prime256) * (as_nat h0 x % prime256)) prime256}
  
    (as_nat h0 x * ((as_nat h0 x % prime256) * (as_nat h0 x % prime256)) % prime256 - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;

    (==) {
      assert_by_tactic (as_nat h0 x * ((as_nat h0 x % prime256) * (as_nat h0 x % prime256)) == 
	(as_nat h0 x % prime256 * (as_nat h0 x * (as_nat h0 x % prime256)))) canon;
      lemma_mod_mul_distr_l (as_nat h0 x) (as_nat h0 x * (as_nat h0 x % prime256)) prime256}

    (as_nat h0 x * (as_nat h0 x * (as_nat h0 x % prime256)) % prime256 - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;

    (==) {
      assert_by_tactic (as_nat h0 x * (as_nat h0 x * (as_nat h0 x % prime256)) == (as_nat h0 x % prime256) * (as_nat h0 x * as_nat h0 x)) canon;
      lemma_mod_mul_distr_l (as_nat h0 x) (as_nat h0 x * as_nat h0 x) prime256;
      assert_by_tactic ((as_nat h0 x) * (as_nat h0 x * as_nat h0 x) == as_nat h0 x * as_nat h0 x * as_nat h0 x) canon
    }

    ((as_nat h0 x * as_nat h0 x * as_nat h0 x) % prime256 - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;
    (==) {lemma_mod_add_distr (- (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) (as_nat h0 x * as_nat h0 x * as_nat h0 x) prime256}
    (as_nat h0 x * as_nat h0 x * as_nat h0 x - (3 * as_nat h0 x) + Spec.P256.bCoordinateP256) % prime256;
    };
  r

  

val verifyQValidCurvePointPrivate: pubKeyAsPoint:point
  -> tempBuffer:lbuffer uint64 (size 100) -> Stack uint64
  (requires fun h -> 
    live h pubKeyAsPoint /\
    live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc tempBuffer] /\
    point_z_as_nat h pubKeyAsPoint == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (v r = 0 \/ v r == ones_v U64) /\ (
    v r == pow2 64 - 1 <==> verifyQValidCurvePointSpec (point_prime_to_coordinates (as_seq h0 pubKeyAsPoint))))


let verifyQValidCurvePointPrivate pubKeyAsPoint tempBuffer =  
  let coordinatesValid = isCoordinateValidPrivate pubKeyAsPoint in 
  let belongsToCurve = isPointOnCurvePrivate pubKeyAsPoint tempBuffer in 
  logand_lemma coordinatesValid belongsToCurve;
  logand coordinatesValid belongsToCurve



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
  let publicKeyCorrect_u64 = verifyQValidCurvePointPrivate publicKeyBuffer tempBuffer in
  let publicKeyCorrect = Hacl.Impl.P256.LowLevel.RawCmp.unsafe_bool_of_u64 publicKeyCorrect_u64 in
  if not publicKeyCorrect then
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


let ecp256scalar_mult result pubKey scalar =
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

  let flag = _ecp256scalar_mult resultBufferFelem publicKeyAsFelem scalar in

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

