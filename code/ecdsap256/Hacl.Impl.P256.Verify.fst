module Hacl.Impl.P256.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.P256
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.MontgomeryMultiplication
open Spec.ECDSA

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble
open Hacl.Impl.P256.RawCmp
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Qinv
open Hacl.Impl.P256.PointMul
open Hacl.Impl.P256.Constants

open Hacl.Hash.SHA2
open Spec.Hash.Definitions

module S = Spec.P256

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


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


[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val isMoreThanZeroLessThanOrderMinusOne: f:felem -> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r = (as_nat h0 f > 0 && as_nat h0 f < order))

let isMoreThanZeroLessThanOrderMinusOne f =
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in
    recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
  let carry = bn_sub4_il f primeorder_buffer tempBuffer in
  let less = eq_u64_nCT carry (u64 1) in
  let more = isZero_uint64_nCT f in
  let result = less && not more in
  pop_frame();
  result


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


inline_for_extraction
val ecdsa_verification_step23: alg:hash_alg_ecdsa
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length alg}
  -> m: lbuffer uint8 mLen
  -> result: felem
  -> Stack unit
    (requires fun h -> live h m /\ live h result )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
	assert_norm (pow2 32 < pow2 61);
	assert_norm (pow2 32 < pow2 125);
	let hashM = hashSpec alg (v mLen) (as_seq h0 m) in
	let cutHashM = Lib.Sequence.sub hashM 0 32 in
	as_nat h1 result = nat_from_bytes_be cutHashM % order
      )
    )


let ecdsa_verification_step23 alg mLen m result =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
  let sz: FStar.UInt32.t = match alg with |NoHash -> mLen |Hash a -> Hacl.Hash.Definitions.hash_len a in
  let mHash = create sz (u8 0) in

  begin
  match alg with
    |NoHash -> copy mHash m
    |Hash a -> match a with
      |SHA2_256 -> hash_256 m mLen mHash
      |SHA2_384 -> hash_384 m mLen mHash
      |SHA2_512 -> hash_512 m mLen mHash
  end;

  let cutHash = sub mHash (size 0) (size 32) in
  bn_from_bytes_be4 cutHash result;
  let h1 = ST.get() in
  qmod_short result result;

    lemma_core_0 result h1;
    Spec.ECDSA.changeEndianLemma (uints_from_bytes_be #U64 #_ #4 (as_seq h1 cutHash));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 cutHash);

  pop_frame()



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
      as_nat h s < order /\
      as_nat h hash < order /\
      as_nat h r < order
    )
    (ensures fun h0 _ h1 ->
      modifies (loc bufferU1 |+| loc bufferU2) h0 h1 /\
      (
	let p0 = pow (as_nat h0 s) (order - 2) * as_nat h0 hash % order in
	let p1 = pow (as_nat h0 s) (order - 2) * as_nat h0 r % order in
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
    qinv inverseS;
    multPowerPartial s inverseS hash u1;
    multPowerPartial s inverseS r u2;

  let h1 = ST.get() in
    Hacl.Impl.P256.Bignum.changeEndian u1;
    Hacl.Impl.P256.Bignum.changeEndian u2;
    bn_to_bytes_be4 u1 bufferU1;
    bn_to_bytes_be4 u2 bufferU2;

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
      point_x_as_nat h pubKeyAsPoint < prime /\
      point_y_as_nat h pubKeyAsPoint < prime /\
      point_z_as_nat h pubKeyAsPoint < prime
    )
  (ensures fun h0 _ h1 ->
    modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc points) h0 h1 /\
    as_nat h1 (gsub points (size 0) (size 4)) < prime /\
    as_nat h1 (gsub points (size 4) (size 4)) < prime /\
    as_nat h1 (gsub points (size 8) (size 4)) < prime /\
    as_nat h1 (gsub points (size 12) (size 4)) < prime /\
    as_nat h1 (gsub points (size 16) (size 4)) < prime /\
    as_nat h1 (gsub points (size 20) (size 4)) < prime /\
    (
      let pointU1 = gsub points (size 0) (size 12) in
      let pointU2 = gsub points (size 12) (size 12) in

      let fromDomainPointU1 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU1)) in
      let fromDomainPointU2 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU2)) in
      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, base_point) in
      let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
      fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D
    )
  )

let ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2 tempBuffer =
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in
  secretToPublicWithoutNorm pointU1G u1 tempBuffer;
  scalarMultiplicationWithoutNorm pubKeyAsPoint pointU2Q u2 tempBuffer


[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val compare_felem_bool: a: felem -> b: felem -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat h0 a = as_nat h0 b))

let compare_felem_bool a b  =
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

  eq_u64_nCT a_0 b_0 &&
  eq_u64_nCT a_1 b_1 &&
  eq_u64_nCT a_2 b_2 &&
  eq_u64_nCT a_3 b_3



inline_for_extraction noextract
val compare_points_bool: a: point -> b: point -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (
      let xP = gsub a (size 0) (size 4) in
      let yP = gsub a (size 4) (size 4) in
      let zP = gsub a (size 8) (size 4) in

      let xQ = gsub b (size 0) (size 4) in
      let yQ = gsub b (size 4) (size 4) in
      let zQ = gsub b (size 8) (size 4) in

      r == ((as_nat h0 xP = as_nat h0 xQ) && (as_nat h0 yP = as_nat h0 yQ) && (as_nat h0 zP = as_nat h0 zQ))
    )
  )

let compare_points_bool a b =
  let x0 = sub a (size 0) (size 4) in
  let y0 = sub a (size 4) (size 4) in
  let z0 = sub a (size 8) (size 4) in

  let x1 = sub b (size 0) (size 4) in
  let y1 = sub b (size 4) (size 4) in
  let z1 = sub b (size 8) (size 4) in

  let xEqual = compare_felem_bool x0 x1 in
  let yEqual = compare_felem_bool y0 y1 in
  let zEqual = compare_felem_bool z0 z1 in
  xEqual && yEqual && zEqual


inline_for_extraction noextract
val ecdsa_verification_step5_1: points:lbuffer uint64 (size 24) -> Stack bool
  (requires fun h -> live h points /\
    as_nat h (gsub points (size 0) (size 4)) < prime /\
    as_nat h (gsub points (size 4) (size 4)) < prime /\
    as_nat h (gsub points (size 8) (size 4)) < prime /\
    as_nat h (gsub points (size 12) (size 4)) < prime /\
    as_nat h (gsub points (size 16) (size 4)) < prime /\
    as_nat h (gsub points (size 20) (size 4)) < prime
  )
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (
      let pointU1G = gsub points (size 0) (size 12) in
      let pointU2Q = gsub points (size 12) (size 12) in
      r = (
	norm_jacob_point (fromDomainPoint (point_prime_to_coordinates (as_seq h0 pointU1G))) =
	norm_jacob_point (fromDomainPoint (point_prime_to_coordinates (as_seq h0 pointU2Q))))
    )
  )

let ecdsa_verification_step5_1 points =
  push_frame();

  let tmp = create (size 112) (u64 0) in
  let tmpForNorm = sub tmp (size 0) (size 88) in
  let result0Norm = sub tmp (size 88) (size 12) in
  let result1Norm = sub tmp (size 100) (size 12) in
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in

  norm pointU1G result0Norm tmpForNorm;
  norm pointU2Q result1Norm tmpForNorm;
  let equalX = compare_points_bool result0Norm result1Norm in

  pop_frame();
  equalX



inline_for_extraction noextract
val ecdsa_verification_step5_2:
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
      point_x_as_nat h pubKeyAsPoint < prime /\
      point_y_as_nat h pubKeyAsPoint < prime /\
      point_z_as_nat h pubKeyAsPoint < prime
    )
    (ensures fun h0 _ h1 ->
      modifies (loc pointSum |+| loc tempBuffer |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat h1 (gsub pointSum (size 0) (size 4)) < prime /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, base_point) in
        let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
	let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
        let pointNorm = norm_jacob_point sumD in
        let resultPoint =  point_prime_to_coordinates (as_seq h1 pointSum) in
        pointNorm == resultPoint
      )
   )


let ecdsa_verification_step5_2 pointSum pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let points = create (size 24) (u64 0) in
  let buff = sub tempBuffer (size 12) (size 88) in
  ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2 tempBuffer;
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in

  let equalX = ecdsa_verification_step5_1 points in
  begin
  if equalX then
  	point_double pointU1G pointSum buff
  else
  	point_add pointU1G pointU2Q pointSum buff end;
  norm pointSum pointSum buff;
  pop_frame()


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
      point_x_as_nat h pubKeyAsPoint < prime /\
      point_y_as_nat h pubKeyAsPoint < prime /\
      point_z_as_nat h pubKeyAsPoint < prime
    )
    (ensures fun h0 state h1 ->
      modifies (loc x |+| loc pubKeyAsPoint |+| loc tempBuffer) h0 h1 /\
      as_nat h1 x < prime /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, base_point) in
        let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
        let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
        let pointNorm = norm_jacob_point sumD in
        let (xResult, yResult, zResult) = pointNorm in
        state == not (Spec.P256.isPointAtInfinity pointNorm) /\
        as_nat h1 x == xResult % order
    )
  )

let ecdsa_verification_step5 x pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let pointSum = create (size 12) (u64 0) in
  ecdsa_verification_step5_2 pointSum pubKeyAsPoint u1 u2 tempBuffer;
  let resultIsPAI = isPointAtInfinityPublic pointSum in
  let xCoordinateSum = sub pointSum (size 0) (size 4) in
  copy x xCoordinateSum;
  qmod_short x x;
  pop_frame();
  not resultIsPAI


inline_for_extraction
val ecdsa_verification_core:
  alg:hash_alg_ecdsa
  -> publicKeyPoint:point
  -> hashAsFelem:felem
  -> r:lbuffer uint64 (size 4)
  -> s:lbuffer uint64 (size 4)
  -> mLen:size_t{v mLen >= Spec.ECDSA.min_input_length alg}
  -> m:lbuffer uint8 mLen
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
      as_nat h s < order /\ as_nat h r < order /\
      point_x_as_nat h publicKeyPoint < prime /\
      point_y_as_nat h publicKeyPoint < prime /\
      point_z_as_nat h publicKeyPoint < prime
    )
    (ensures fun h0 state h1 ->
      modifies (loc publicKeyPoint |+| loc hashAsFelem |+| loc xBuffer |+| loc tempBuffer) h0 h1 /\
       (
         assert_norm (pow2 32 < pow2 61);
	 assert_norm (pow2 32 < pow2 125);

	 let hashM = hashSpec alg (v mLen) (as_seq h0 m) in
	 let cutHashM = Lib.Sequence.sub hashM 0 32 in
	 let hashNat =  nat_from_bytes_be cutHashM % order in

         let p0 = pow (as_nat h0 s) (order - 2) * hashNat % order in
	 let p1 = pow (as_nat h0 s) (order - 2) * as_nat h0 r % order in

	 let bufferU1 = nat_to_bytes_be 32 p0  in
	 let bufferU2 = nat_to_bytes_be 32 p1 in
	 let pointAtInfinity = (0, 0, 0) in
         let u1D, _ = montgomery_ladder_spec bufferU1 (pointAtInfinity, base_point) in
         let u2D, _ = montgomery_ladder_spec bufferU2 (pointAtInfinity, point_prime_to_coordinates (as_seq h0 publicKeyPoint)) in
          let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
         let (xResult, yResult, zResult) = norm_jacob_point sumD in
         state == not (Spec.P256.isPointAtInfinity (norm_jacob_point sumD)) /\
         as_nat h1 xBuffer == xResult % order
      )
  )

let ecdsa_verification_core alg publicKeyBuffer hashAsFelem r s mLen m xBuffer tempBuffer =
  assert_norm (pow2 32 < pow2 61 - 1);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
  let tempBufferU8 = create (size 64) (u8 0) in
  let bufferU1 = sub tempBufferU8 (size 0) (size 32) in
  let bufferU2 = sub tempBufferU8 (size 32) (size 32) in
  ecdsa_verification_step23 alg mLen m hashAsFelem;
  ecdsa_verification_step4  bufferU1 bufferU2 r s hashAsFelem;
  let r = ecdsa_verification_step5 xBuffer publicKeyBuffer bufferU1 bufferU2 tempBuffer in
  pop_frame();
  r


[@ (Comment "   The input of the function is considered to be public,
thus this code is not secret independent with respect to the operations done over the input.")]
val ecdsa_verification_:alg:hash_alg_ecdsa
  -> pubKey:lbuffer uint64 (size 8)
  -> r:lbuffer uint64 (size 4)
  -> s: lbuffer uint64 (size 4)
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length alg}
  -> m:lbuffer uint8 mLen ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let pubKeyX = as_nat h0 (gsub pubKey (size 0) (size 4)) in
      let pubKeyY = as_nat h0 (gsub pubKey (size 4) (size 4)) in
      let r = as_nat h0 r in
      let s = as_nat h0 s in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile alg (pubKeyX, pubKeyY) r s (v mLen) (as_seq h0 m))

let ecdsa_verification_ alg pubKey r s mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
  let tempBufferU64 = create (size 120) (u64 0) in
  let publicKeyBuffer = sub tempBufferU64 (size 0) (size 12) in
  let hashAsFelem = sub tempBufferU64 (size 12) (size 4) in
  let tempBuffer = sub tempBufferU64 (size 16) (size 100) in
  let xBuffer = sub tempBufferU64 (size 116) (size 4) in

  bufferToJac pubKey publicKeyBuffer;
  let publicKeyCorrect = verifyQValidCurvePoint publicKeyBuffer in
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
      let state = ecdsa_verification_core alg publicKeyBuffer hashAsFelem r s mLen m xBuffer tempBuffer in
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


inline_for_extraction
val ecdsa_verification:
  alg:hash_alg_ecdsa
  -> pubKey:lbuffer uint8 (size 64)
  -> r:lbuffer uint8 (size 32)
  -> s:lbuffer uint8 (size 32)
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length alg}
  -> m:lbuffer uint8 mLen ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile alg (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m))

let ecdsa_verification alg pubKey r s mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
  let h0 = ST.get() in
  let publicKeyAsFelem = create (size 8) (u64 0) in
  let publicKeyFelemX = sub publicKeyAsFelem (size 0) (size 4) in
  let publicKeyFelemY = sub publicKeyAsFelem (size 4) (size 4) in
  let rAsFelem = create (size 4) (u64 0) in
  let sAsFelem = create (size 4) (u64 0) in
  let pubKeyX = sub pubKey (size 0) (size 32) in
  let pubKeyY = sub pubKey (size 32) (size 32) in

  bn_from_bytes_be4 pubKeyX publicKeyFelemX;
  bn_from_bytes_be4 pubKeyY publicKeyFelemY;

  bn_from_bytes_be4 r rAsFelem;
  bn_from_bytes_be4 s sAsFelem;

  let h1 = ST.get() in
    lemma_core_0 publicKeyFelemX h1;
    uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);
    lemma_core_0 publicKeyFelemY h1;
    uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY);

    lemma_core_0 rAsFelem h1;
    uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 r);
    lemma_core_0 sAsFelem h1;
    uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 s);

  let result = ecdsa_verification_ alg publicKeyAsFelem rAsFelem sAsFelem mLen m in
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
