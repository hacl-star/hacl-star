module Hacl.Impl.ECDSA.P256SHA256.Verification.Hashless

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Lemmas

open Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Impl.P256
open Spec.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent
open Spec.P256.Ladder

open Spec.ECDSAP256.Definition
open Spec.ECDSA
open Spec.P256
open Spec.P256.Lemmas

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.LowLevel.RawCmp

open Hacl.Hash.SHA2

open Hacl.Impl.P256.Signature.Common
open Lib.ByteSequence
open Lib.IntVector.Intrinsics

open Spec.Blake2
open Hacl.Blake2b_32

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open FStar.Mul

module H = Spec.Agile.Hash
module Def = Spec.Hash.Definitions

#set-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(* https://blenderartists.org/uploads/default/original/4X/8/e/b/8eb44765c0060fb9a6f6cbc0a7b1cd2dcd92dbc8.jpg *)

(* This code is not side channel resistant *)
inline_for_extraction noextract
val isZero_uint64_nCT: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat h0 f = 0))

let isZero_uint64_nCT f =
    let f0 = index f (size 0) in
    let f1 = index f (size 1) in
    let f2 = index f (size 2) in
    let f3 = index f (size 3) in

    let z0_zero = eq_0_u64 f0 in
    let z1_zero = eq_0_u64 f1 in
    let z2_zero = eq_0_u64 f2 in
    let z3_zero = eq_0_u64 f3 in

    z0_zero && z1_zero && z2_zero && z3_zero


(* This code is not side channel resistant *)
val isMoreThanZeroLessThanOrderMinusOne: f:felem -> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r = (as_nat h0 f > 0 && as_nat h0 f < prime_p256_order))

let isMoreThanZeroLessThanOrderMinusOne f =
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in
  recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
  let carry = sub4_il f prime256order_buffer tempBuffer in
  let less = eq_u64_nCT carry (u64 1) in
  let more = isZero_uint64_nCT f in
  let result = less && not more in
  pop_frame();
  result


(* Verify that {\displaystyle r} r and {\displaystyle s} s are integers in {\displaystyle [1,n-1]} [1,n-1]. If not, the signature is invalid. *)

inline_for_extraction noextract
val ecdsa_verification_step1: r:lbuffer uint64 (size 4) -> s:lbuffer uint64 (size 4) -> Stack bool
  (requires fun h -> live h r /\ live h s)
  (ensures  fun h0 result h1 ->
    modifies0 h0 h1 /\
    result == checkCoordinates (as_nat h0 r) (as_nat h0 s))

let ecdsa_verification_step1 r s =
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne r in
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne s in
  isRCorrect && isSCorrect


val ecdsa_verification_step23: 
  m: lbuffer uint8 (size 32) -> result: felem -> Stack unit
  (requires fun h -> live h m /\ live h result /\ disjoint m result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    (
      as_nat h1 result = nat_from_bytes_be (as_seq h0 m) % prime_p256_order
    )
  )


let ecdsa_verification_step23 m result = 
  let h0 = ST.get() in 
  toUint64ChangeEndian m result;
    let h1 = ST.get() in 
  reduction_prime_2prime_order result result;
    let h2 = ST.get() in 
  lemma_core_0 result h1;
    
  Spec.ECDSA.changeEndianLemma (uints_from_bytes_be #U64 #_ #4 (as_seq h0 m));
  uints_from_bytes_be_nat_lemma #U64 #SEC #4 (as_seq h0 m)
  

inline_for_extraction noextract
val ecdsa_verification_step4:
    bufferU1:lbuffer uint8 (size 32)
  -> bufferU2: lbuffer uint8 (size 32)
  -> r:felem
  -> s:felem
  -> hash:felem ->
  Stack unit
    (requires fun h ->
      live h r /\ live h s /\ live h hash /\ live h bufferU1 /\ live h bufferU2 /\
      disjoint bufferU1 bufferU2 /\
      disjoint bufferU1 hash /\
      disjoint bufferU1 r /\
      disjoint bufferU1 s /\
      disjoint bufferU2 hash /\
      disjoint bufferU2 r /\
      disjoint bufferU2 s /\
      as_nat h s < prime_p256_order /\
      as_nat h hash < prime_p256_order /\
      as_nat h r < prime_p256_order
    )
    (ensures fun h0 _ h1 ->
      modifies (loc bufferU1 |+| loc bufferU2) h0 h1 /\
      (
	let p0 = pow (as_nat h0 s) (prime_p256_order - 2) * as_nat h0 hash % prime_p256_order in 
	let p1 = pow (as_nat h0 s) (prime_p256_order - 2) * as_nat h0 r % prime_p256_order in 
	as_seq h1 bufferU1 == nat_to_bytes_be 32 p0 /\
	as_seq h1 bufferU2 == nat_to_bytes_be 32 p1
      )
    )

let ecdsa_verification_step4 bufferU1 bufferU2 r s hash =
  push_frame();
  let h0 = ST.get() in
    let tempBuffer = create (size 12) (u64 0) in
    let inverseS = sub tempBuffer (size 0) (size 4) in
    let u1 = sub tempBuffer (size 4) (size 4) in
    let u2 = sub tempBuffer (size 8) (size 4) in

    fromDomainImpl s inverseS;
    montgomery_ladder_exponent inverseS;
    multPowerPartial s inverseS hash u1;
    multPowerPartial s inverseS r u2;
  
  let h1 = ST.get() in 
    Hacl.Impl.LowLevel.changeEndian u1;
    Hacl.Impl.LowLevel.changeEndian u2;
    toUint8 u1 bufferU1;
    toUint8 u2 bufferU2;
  
  let h2 = ST.get() in

    calc(==) {
    as_seq h2 bufferU1;
    == {}
    uints_to_bytes_be (Spec.ECDSA.changeEndian (as_seq h1 u1));
    == {lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h1 u1)}
    uints_to_bytes_be (Spec.ECDSA.changeEndian (nat_to_intseq_le 4 (nat_from_intseq_le (as_seq h1 u1))));
    == {lemma_core_0 u1 h1}
    uints_to_bytes_be (Spec.ECDSA.changeEndian (nat_to_intseq_le 4 (as_nat h1 u1)));
    == { changeEndian_le_be (as_nat h1 u1) }
    nat_to_bytes_be 32 (as_nat h1 u1);
    };

    calc(==) {
      as_seq h2 bufferU2;
      == {}
      uints_to_bytes_be (Spec.ECDSA.changeEndian (as_seq h1 u2));
      == {lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h1 u2)}
      uints_to_bytes_be (Spec.ECDSA.changeEndian (nat_to_intseq_le 4 (nat_from_intseq_le (as_seq h1 u2))));
      == {lemma_core_0 u2 h1}
      uints_to_bytes_be (Spec.ECDSA.changeEndian (nat_to_intseq_le 4 (as_nat h1 u2)));
      == { changeEndian_le_be (as_nat h1 u2) }
      nat_to_bytes_be 32 (as_nat h1 u2);
    };

  pop_frame()



inline_for_extraction noextract
val ecdsa_verification_step5_0:
    points:lbuffer uint64 (size 24)
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32)
  -> tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h ->
      live h points /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\
      disjoint points u1 /\
      disjoint points u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint tempBuffer u1 /\
      disjoint tempBuffer u2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc points; loc pubKeyAsPoint; loc tempBuffer] /\
      point_x_as_nat h pubKeyAsPoint < prime256 /\
      point_y_as_nat h pubKeyAsPoint < prime256 /\
      point_z_as_nat h pubKeyAsPoint < prime256
    )
  (ensures fun h0 _ h1 ->
    modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc points) h0 h1 /\
    as_nat h1 (gsub points (size 0) (size 4)) < prime256 /\
    as_nat h1 (gsub points (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub points (size 8) (size 4)) < prime256 /\
    as_nat h1 (gsub points (size 12) (size 4)) < prime256 /\
    as_nat h1 (gsub points (size 16) (size 4)) < prime256 /\
    as_nat h1 (gsub points (size 20) (size 4)) < prime256 /\
    (
      let pointU1 = gsub points (size 0) (size 12) in
      let pointU2 = gsub points (size 12) (size 12) in

      let fromDomainPointU1 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU1)) in
      let fromDomainPointU2 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU2)) in
      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in
      let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
      fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D
    )
  )

let ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2 tempBuffer =
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in
  secretToPublicWithoutNorm pointU1G u1 tempBuffer;
  scalarMultiplicationWithoutNorm pubKeyAsPoint pointU2Q u2 tempBuffer


inline_for_extraction noextract
val ecdsa_verification_step5_1:
    pointSum: point
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32)
  -> tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h ->
      live h pointSum /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\
      disjoint pointSum u1 /\
      disjoint pointSum u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint tempBuffer u1 /\
      disjoint tempBuffer u2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc pointSum; loc pubKeyAsPoint; loc tempBuffer] /\
      point_x_as_nat h pubKeyAsPoint < prime256 /\
      point_y_as_nat h pubKeyAsPoint < prime256 /\
      point_z_as_nat h pubKeyAsPoint < prime256
    )
    (ensures fun h0 _ h1 ->
      modifies (loc pointSum |+| loc tempBuffer |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat h1 (gsub pointSum (size 0) (size 4)) < prime256 /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in
        let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
        let sumD = _point_add u1D u2D in
        let pointNorm = _norm sumD in
        let resultPoint =  point_prime_to_coordinates (as_seq h1 pointSum) in
        pointNorm == resultPoint
      )
   )

let ecdsa_verification_step5_1 pointSum pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let points = create (size 24) (u64 0) in
  let buff = sub tempBuffer (size 12) (size 88) in
  ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2 tempBuffer;
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in
  point_add pointU1G pointU2Q pointSum buff;
  norm pointSum pointSum buff;
  pop_frame()


(* This code is not side channel resistant *)
inline_for_extraction noextract
val ecdsa_verification_step5:
    x:felem
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32)
  -> tempBuffer: lbuffer uint64 (size 100) ->
  Stack bool
    (requires fun h ->
      live h x /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\
      disjoint x u1 /\
      disjoint x u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint tempBuffer u1 /\
      disjoint tempBuffer u2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc x; loc pubKeyAsPoint; loc tempBuffer] /\
      point_x_as_nat h pubKeyAsPoint < prime256 /\
      point_y_as_nat h pubKeyAsPoint < prime256 /\
      point_z_as_nat h pubKeyAsPoint < prime256
    )
    (ensures fun h0 state h1 ->
      modifies (loc x |+| loc pubKeyAsPoint |+| loc tempBuffer) h0 h1 /\
      as_nat h1 x < prime256 /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in
        let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
        let sumD = _point_add u1D u2D in
        let pointNorm = _norm sumD in
        let (xResult, yResult, zResult) = pointNorm in
        state == not (Spec.P256.isPointAtInfinity pointNorm) /\
        as_nat h1 x == xResult
    )
  )

let ecdsa_verification_step5 x pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let pointSum = create (size 12) (u64 0) in
  ecdsa_verification_step5_1 pointSum pubKeyAsPoint u1 u2 tempBuffer;
  let resultIsPAI = isPointAtInfinityPublic pointSum in
  let xCoordinateSum = sub pointSum (size 0) (size 4) in
  copy x xCoordinateSum;
  pop_frame();
  not resultIsPAI

val lemma_compare: a: felem -> b: felem -> h: mem ->  Lemma 
  (
    let a0 = Lib.Sequence.index (as_seq h a) 0 in 
    let a1 = Lib.Sequence.index (as_seq h a) 1 in 
    let a2 = Lib.Sequence.index (as_seq h a) 2 in 
    let a3 = Lib.Sequence.index (as_seq h a) 3 in 

    let b0 = Lib.Sequence.index (as_seq h b) 0 in 
    let b1 = Lib.Sequence.index (as_seq h b) 1 in 
    let b2 = Lib.Sequence.index (as_seq h b) 2 in 
    let b3 = Lib.Sequence.index (as_seq h b) 3 in 

     if v a0 = v b0 &&  v a1 = v b1 && v a2 = v b2 && v a3 = v b3 then  as_nat h a = as_nat h b else True
  )

let lemma_compare a b h = 
  assert(
    let a0 = Lib.Sequence.index (as_seq h a) 0 in 
    let a1 = Lib.Sequence.index (as_seq h a) 1 in 
    let a2 = Lib.Sequence.index (as_seq h a) 2 in 
    let a3 = Lib.Sequence.index (as_seq h a) 3 in 
    as_nat h a = v a0 + v a1 * pow2 64 + v a2 * pow2 64 * pow2 64 + v a3 * pow2 64 * pow2 64 * pow2 64);

  assert(
    let a0 = Lib.Sequence.index (as_seq h b) 0 in 
    let a1 = Lib.Sequence.index (as_seq h b) 1 in 
    let a2 = Lib.Sequence.index (as_seq h b) 2 in 
    let a3 = Lib.Sequence.index (as_seq h b) 3 in 
    as_nat h b = v a0 + v a1 * pow2 64 + v a2 * pow2 64 * pow2 64 + v a3 * pow2 64 * pow2 64 * pow2 64)


(* to use with care - not SCA resistant, so used only in verification *)
val compare_felem_bool: a: felem -> b: felem -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat h0 a = as_nat h0 b))

let compare_felem_bool a b   =
  assert_norm (pow2 64 * pow2 64 == pow2 128);
  assert_norm (pow2 128 * pow2 64 == pow2 192);
  let a_0 = index a (size 0) in
  let a_1 = index a (size 1) in
  let a_2 = index a (size 2) in
  let a_3 = index a (size 3) in

  let b_0 = index b (size 0) in
  let b_1 = index b (size 1) in
  let b_2 = index b (size 2) in
  let b_3 = index b (size 3) in

  let h = ST.get() in 

  lemma_compare a b h;

  eq_u64_nCT a_0 b_0 &&
  eq_u64_nCT a_1 b_1 &&
  eq_u64_nCT a_2 b_2 &&
  eq_u64_nCT a_3 b_3


val ecdsa_verification_core:
  publicKeyPoint:point
  -> hashAsFelem:felem
  -> r:lbuffer uint64 (size 4)
  -> s:lbuffer uint64 (size 4)
  -> m:lbuffer uint8 (size 32)
  -> xBuffer:felem
  -> tempBuffer:lbuffer uint64 (size 100) ->
  Stack bool
    (requires fun h ->
      live h publicKeyPoint /\ live h hashAsFelem /\ live h r /\ live h s /\ live h m /\ live h xBuffer /\ live h tempBuffer /\
      disjoint publicKeyPoint r /\
      disjoint publicKeyPoint s /\
      disjoint publicKeyPoint m /\
      disjoint hashAsFelem r /\
      disjoint hashAsFelem s /\
      disjoint hashAsFelem m /\
      disjoint xBuffer r /\
      disjoint xBuffer s /\
      disjoint xBuffer m /\
      disjoint tempBuffer r /\
      disjoint tempBuffer s /\
      disjoint tempBuffer m /\
      LowStar.Monotonic.Buffer.all_disjoint [loc publicKeyPoint; loc hashAsFelem; loc xBuffer; loc tempBuffer] /\
      as_nat h s < prime_p256_order /\ as_nat h r < prime_p256_order /\
      point_x_as_nat h publicKeyPoint < prime256 /\
      point_y_as_nat h publicKeyPoint < prime256 /\
      point_z_as_nat h publicKeyPoint < prime256
    )
    (ensures fun h0 state h1 ->
      modifies (loc publicKeyPoint |+| loc hashAsFelem |+| loc xBuffer |+| loc tempBuffer) h0 h1 /\
       (
         assert_norm (pow2 32 < pow2 61);
	 assert_norm (pow2 32 < pow2 125);
	 
	 let hashNat  = nat_from_bytes_be (as_seq h0 m) % prime_p256_order in 

         let p0 = pow (as_nat h0 s) (prime_p256_order - 2) * hashNat % prime_p256_order in 
	 let p1 = pow (as_nat h0 s) (prime_p256_order - 2) * as_nat h0 r % prime_p256_order in 

	 let bufferU1 = nat_to_bytes_be 32 p0  in 
	 let bufferU2 = nat_to_bytes_be 32 p1 in 
	 let pointAtInfinity = (0, 0, 0) in
         let u1D, _ = montgomery_ladder_spec bufferU1 (pointAtInfinity, basePoint) in
         let u2D, _ = montgomery_ladder_spec bufferU2 (pointAtInfinity, point_prime_to_coordinates (as_seq h0 publicKeyPoint)) in
         let sumD = _point_add u1D u2D in
         let (xResult, yResult, zResult) = _norm sumD in
         state == not (Spec.P256.isPointAtInfinity (_norm sumD)) /\
         as_nat h1 xBuffer == xResult
      )
  )


let ecdsa_verification_core publicKeyBuffer hashAsFelem r s m xBuffer tempBuffer =
  push_frame();
  let tempBufferU8 = create (size 64) (u8 0) in
  let bufferU1 = sub tempBufferU8 (size 0) (size 32) in
  let bufferU2 = sub tempBufferU8 (size 32) (size 32) in
  ecdsa_verification_step23 m hashAsFelem;
  ecdsa_verification_step4  bufferU1 bufferU2 r s hashAsFelem;
  let r = ecdsa_verification_step5 xBuffer publicKeyBuffer bufferU1 bufferU2 tempBuffer in
  pop_frame();
  r


(* This code is not side channel resistant *)
val ecdsa_verification_:
  pubKey:lbuffer uint64 (size 8)
  -> r:lbuffer uint64 (size 4)
  -> s: lbuffer uint64 (size 4)
  -> m:lbuffer uint8 (size 32) ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      let pubKeyX = as_nat h0 (gsub pubKey (size 0) (size 4)) in
      let pubKeyY = as_nat h0 (gsub pubKey (size 4) (size 4)) in
      let r = as_nat h0 r in
      let s = as_nat h0 s in
      modifies0 h0 h1 /\
      result == ecdsa_verification_without_hash (pubKeyX, pubKeyY) r s  (as_seq h0 m))


let ecdsa_verification_  pubKey r s m =
  push_frame();
  let tempBufferU64 = create (size 120) (u64 0) in
  let publicKeyBuffer = sub tempBufferU64 (size 0) (size 12) in
  let hashAsFelem = sub tempBufferU64 (size 12) (size 4) in
  let tempBuffer = sub tempBufferU64 (size 16) (size 100) in
  let xBuffer = sub tempBufferU64 (size 116) (size 4) in

  bufferToJac pubKey publicKeyBuffer;
  let publicKeyCorrect = verifyQValidCurvePoint publicKeyBuffer tempBuffer in
  if publicKeyCorrect = false then
    begin
    pop_frame();
    false
    end
  else
    let step1 = ecdsa_verification_step1 r s in
    if step1 = false then
      begin
      pop_frame();
      false
      end
    else
      let state = ecdsa_verification_core publicKeyBuffer hashAsFelem r s  m xBuffer tempBuffer in
      if state = false then
        begin
        pop_frame();
        false
        end
      else
        begin
        let result = compare_felem_bool xBuffer r in
        pop_frame();
        result
        end


val ecdsa_verification_without_hash:
  pubKey:lbuffer uint8 (size 64)
  -> r:lbuffer uint8 (size 32)
  -> s:lbuffer uint8 (size 32)
  -> m:lbuffer uint8 (size 32) ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_without_hash (publicKeyX, publicKeyY) r s  (as_seq h0 m))

let ecdsa_verification_without_hash pubKey r s m =
  push_frame();
  let h0 = ST.get() in 
    let publicKeyAsFelem = create (size 8) (u64 0) in
      let publicKeyFelemX = sub publicKeyAsFelem (size 0) (size 4) in 
      let publicKeyFelemY = sub publicKeyAsFelem (size 4) (size 4) in 
    let rAsFelem = create (size 4) (u64 0) in 
    let sAsFelem = create (size 4) (u64 0) in 
      let pubKeyX = sub pubKey (size 0) (size 32) in
      let pubKeyY = sub pubKey (size 32) (size 32) in 
      
    toUint64ChangeEndian pubKeyX publicKeyFelemX;
    toUint64ChangeEndian pubKeyY publicKeyFelemY;
   
    toUint64ChangeEndian r rAsFelem;
    toUint64ChangeEndian s sAsFelem;

  let h1 = ST.get() in 
      lemma_core_0 publicKeyFelemX h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);  
      lemma_core_0 publicKeyFelemY h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY);

      lemma_core_0 rAsFelem h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 r);
      lemma_core_0 sAsFelem h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 s);

    let result = ecdsa_verification_ publicKeyAsFelem rAsFelem sAsFelem  m in 
    pop_frame();

    changeEndianLemma (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));
    
    changeEndianLemma (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));
    
    changeEndianLemma (uints_from_bytes_be (as_seq h1 r));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 r);
    
    changeEndianLemma (uints_from_bytes_be (as_seq h1 s));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 s);

  result
