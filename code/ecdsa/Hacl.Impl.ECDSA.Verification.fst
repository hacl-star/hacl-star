module Hacl.Impl.ECDSA.Verification

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Lemmas.P256

open Hacl.Spec.P256.Definition
open Hacl.Spec.ECDSA.Definition
open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.P256.Core
open Hacl.Spec.P.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent

open Hacl.Spec.ECDSA.Definition
open Spec.ECDSA
open Spec.P256
(* open Spec.P256.Lemmas *)

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel.RawCmp

open Hacl.Hash.SHA2

open Hacl.Impl.P256.Signature.Common
open Lib.ByteSequence
open Lib.IntVector.Intrinsics

open Hacl.Impl.EC.Intro

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open FStar.Mul

module H = Spec.Agile.Hash
module Def = Spec.Hash.Definitions

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


inline_for_extraction noextract
val isZero_uint64_nCT: #c: curve -> f: felem c -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat c h0 f = 0))

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


(* [@ (Comment "  This code is not side channel resistant")] *)

val isMoreThanZeroLessThanOrderMinusOne: #c: curve -> f: felem c-> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r = (as_nat c h0 f > 0 && as_nat c h0 f < prime_p256_order))

let isMoreThanZeroLessThanOrderMinusOne f =
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in
  recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
  let carry = sub_bn_gl #P256 f prime256order_buffer tempBuffer in
  let less = eq_u64_nCT carry (u64 1) in
  let more = isZero_uint64_nCT f in
  let result = less && not more in
  pop_frame();
  result


inline_for_extraction noextract
val ecdsa_verification_step1: #c: curve -> r:lbuffer uint64 (size 4) -> s:lbuffer uint64 (size 4) -> Stack bool
  (requires fun h -> live h r /\ live h s)
  (ensures  fun h0 result h1 ->
    modifies0 h0 h1 /\
    result == checkCoordinates #P256 (as_nat c h0 r) (as_nat c h0 s))

let ecdsa_verification_step1 #c r s =
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne #c r in
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne #c s in
  isRCorrect && isSCorrect


inline_for_extraction
val ecdsa_verification_step23: 
    #c: curve 
  -> alg:hash_alg_ecdsa
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #P256 alg}
  -> m: lbuffer uint8 mLen 
  -> result: felem c
  -> Stack unit
    (requires fun h -> live h m /\ live h result )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
	assert_norm (pow2 32 < pow2 61);
	assert_norm (pow2 32 < pow2 125);
	let hashM = hashSpec P256 alg (v mLen) (as_seq h0 m) in 
	let cutHashM = Lib.Sequence.sub hashM 0 32 in 
	as_nat c h1 result = nat_from_bytes_be cutHashM % prime_p256_order
      )
    )


let ecdsa_verification_step23 #c alg mLen m result = 
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame(); 
    let h0 = ST.get() in 
  let sz: FStar.UInt32.t = match alg with |NoHash -> mLen |Hash a ->  hash_len a in
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
  toUint64ChangeEndian #c cutHash result;
  
  let h1 = ST.get() in 
 
  reduction_prime_2prime_order result result;

  lemma_core_0 c result h1;
  changeEndianLemma #c (uints_from_bytes_be #U64 #_ #4 (as_seq h1 cutHash));
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 cutHash);

  pop_frame()



inline_for_extraction noextract
val ecdsa_verification_step4:
  #c: curve 
  -> bufferU1:lbuffer uint8 (size 32)
  -> bufferU2: lbuffer uint8 (size 32)
  -> r: felem c
  -> s: felem c
  -> hash: felem c ->
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
      as_nat c h s < prime_p256_order /\
      as_nat c h hash < prime_p256_order /\
      as_nat c h r < prime_p256_order
    )
    (ensures fun h0 _ h1 ->
      modifies (loc bufferU1 |+| loc bufferU2) h0 h1 /\
      (
	let p0 = pow (as_nat c h0 s) (prime_p256_order - 2) * as_nat c h0 hash % prime_p256_order in 
	let p1 = pow (as_nat c h0 s) (prime_p256_order - 2) * as_nat c h0 r % prime_p256_order in 
	as_seq h1 bufferU1 == nat_to_bytes_be 32 p0 /\
	as_seq h1 bufferU2 == nat_to_bytes_be 32 p1
      )
    )

let ecdsa_verification_step4 #c bufferU1 bufferU2 r s hash =
  push_frame();
  let h0 = ST.get() in
    let tempBuffer = create (size 12) (u64 0) in
    let inverseS = sub tempBuffer (size 0) (size 4) in
    let u1 = sub tempBuffer (size 4) (size 4) in
    let u2 = sub tempBuffer (size 8) (size 4) in

    fromDomainImpl s inverseS;
    montgomery_ladder_exponent #c inverseS;
    multPowerPartial s inverseS hash u1;
    multPowerPartial s inverseS r u2;
  
  let h1 = ST.get() in 
    changeEndian #c u1;
    changeEndian #c u2;
    toUint8 #c u1 bufferU1;
    toUint8 #c u2 bufferU2;
  
  let h2 = ST.get() in

    calc(==) {
    as_seq h2 bufferU1;
    == {}
    uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (as_seq h1 u1));
    == {lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h1 u1)}
    uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (nat_to_intseq_le 4 (nat_from_intseq_le (as_seq h1 u1))));
    == {lemma_core_0 c u1 h1}
    uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (nat_to_intseq_le 4 (as_nat c h1 u1)));
    == {changeEndian_le_be #c (as_nat c h1 u1) }
    nat_to_bytes_be 32 (as_nat c h1 u1);
    };

    calc(==) {
      as_seq h2 bufferU2;
      == {}
      uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (as_seq h1 u2));
      == {lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h1 u2)}
      uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (nat_to_intseq_le 4 (nat_from_intseq_le (as_seq h1 u2))));
      == {lemma_core_0 c u2 h1}
      uints_to_bytes_be (Hacl.Spec.P256.Definition.changeEndian #c (nat_to_intseq_le 4 (as_nat c h1 u2)));
      == {changeEndian_le_be #c (as_nat c h1 u2) }
      nat_to_bytes_be 32 (as_nat c h1 u2);
    };

  pop_frame()



inline_for_extraction noextract
val ecdsa_verification_step5_0:
  #c: curve 
  -> points:lbuffer uint64 (size 24)
  -> pubKeyAsPoint: point c
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
      point_x_as_nat c h pubKeyAsPoint < prime256 /\
      point_y_as_nat c h pubKeyAsPoint < prime256 /\
      point_z_as_nat c h pubKeyAsPoint < prime256
    )
  (ensures fun h0 _ h1 ->
    modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc points) h0 h1 /\
    as_nat c h1 (gsub points (size 0) (size 4)) < prime256 /\
    as_nat c h1 (gsub points (size 4) (size 4)) < prime256 /\
    as_nat c h1 (gsub points (size 8) (size 4)) < prime256 /\
    as_nat c h1 (gsub points (size 12) (size 4)) < prime256 /\
    as_nat c h1 (gsub points (size 16) (size 4)) < prime256 /\
    as_nat c h1 (gsub points (size 20) (size 4)) < prime256 /\
    (
      let pointU1 = gsub points (size 0) (size 12) in
      let pointU2 = gsub points (size 12) (size 12) in

      let fromDomainPointU1 = fromDomainPoint #c (point_prime_to_coordinates c (as_seq h1 pointU1)) in
      let fromDomainPointU2 = fromDomainPoint #c (point_prime_to_coordinates c (as_seq h1 pointU2)) in
      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec #P256 (as_seq h0 u1) (pointAtInfinity, basePoint #c) in
      let u2D, _ = montgomery_ladder_spec #P256 (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates c (as_seq h0 pubKeyAsPoint)) in
      fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D
    )
  )

let ecdsa_verification_step5_0 #c points pubKeyAsPoint u1 u2 tempBuffer =
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in
  secretToPublicWithoutNorm #c pointU1G u1 tempBuffer;
  scalarMultiplicationWithoutNorm pubKeyAsPoint pointU2Q u2 tempBuffer


inline_for_extraction noextract
val ecdsa_verification_step5_1:
  #c: curve 
  -> pointSum: point c
  -> pubKeyAsPoint: point c
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
      point_x_as_nat c h pubKeyAsPoint < prime256 /\
      point_y_as_nat c h pubKeyAsPoint < prime256 /\
      point_z_as_nat c h pubKeyAsPoint < prime256
    )
    (ensures fun h0 _ h1 ->
      modifies (loc pointSum |+| loc tempBuffer |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat c h1 (gsub pointSum (size 0) (size 4)) < prime256 /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec #c (as_seq h0 u1) (pointAtInfinity, basePoint #P256) in
        let u2D, _ = montgomery_ladder_spec #c (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates c (as_seq h0 pubKeyAsPoint)) in
        let sumD = _point_add #c u1D u2D in
        let pointNorm = _norm #c sumD in
        let resultPoint =  point_prime_to_coordinates c (as_seq h1 pointSum) in
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
  #c: curve 
  -> x: felem c
  -> pubKeyAsPoint: point c
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
      point_x_as_nat c h pubKeyAsPoint < prime256 /\
      point_y_as_nat c h pubKeyAsPoint < prime256 /\
      point_z_as_nat c h pubKeyAsPoint < prime256
    )
    (ensures fun h0 state h1 ->
      modifies (loc x |+| loc pubKeyAsPoint |+| loc tempBuffer) h0 h1 /\
      as_nat c h1 x < prime256 /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec #c (as_seq h0 u1) (pointAtInfinity, basePoint #c) in
        let u2D, _ = montgomery_ladder_spec #c (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates c (as_seq h0 pubKeyAsPoint)) in
        let sumD = _point_add #c u1D u2D in
        let pointNorm = _norm #c sumD in
        let (xResult, yResult, zResult) = pointNorm in
        state == not (Spec.P256.isPointAtInfinity pointNorm) /\
        as_nat c h1 x == xResult
    )
  )

let ecdsa_verification_step5 #c x pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let pointSum = create (size 12) (u64 0) in
  ecdsa_verification_step5_1 pointSum pubKeyAsPoint u1 u2 tempBuffer;
  let resultIsPAI = isPointAtInfinityPublic #c pointSum in
  let xCoordinateSum = sub pointSum (size 0) (size 4) in
  copy x xCoordinateSum;
  pop_frame();
  not resultIsPAI


(* [@ (Comment "  This code is not side channel resistant")] *)

val compare_felem_bool: #c: curve -> a: felem c -> b: felem c -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat c h0 a = as_nat c h0 b))

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


inline_for_extraction
val ecdsa_verification_core:
  #c: curve -> 
  alg:hash_alg_ecdsa
  -> publicKeyPoint:point c
  -> hashAsFelem:felem c
  -> r:lbuffer uint64 (size 4)
  -> s:lbuffer uint64 (size 4)
  -> mLen:size_t{v mLen >= Spec.ECDSA.min_input_length #P256 alg}
  -> m:lbuffer uint8 mLen
  -> xBuffer:felem c
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
      as_nat c h s < prime_p256_order /\ as_nat c h r < prime_p256_order /\
      point_x_as_nat c h publicKeyPoint < prime256 /\
      point_y_as_nat c h publicKeyPoint < prime256 /\
      point_z_as_nat c h publicKeyPoint < prime256
    )
    (ensures fun h0 state h1 ->
      modifies (loc publicKeyPoint |+| loc hashAsFelem |+| loc xBuffer |+| loc tempBuffer) h0 h1 /\
       (
         assert_norm (pow2 32 < pow2 61);
	 assert_norm (pow2 32 < pow2 125);
	 
	 let hashM = hashSpec P256 alg (v mLen) (as_seq h0 m) in 
	 let cutHashM = Lib.Sequence.sub hashM 0 32 in 
	 let hashNat =  nat_from_bytes_be cutHashM % prime_p256_order in 
	 
         let p0 = pow (as_nat c h0 s) (prime_p256_order - 2) * hashNat % prime_p256_order in 
	 let p1 = pow (as_nat c h0 s) (prime_p256_order - 2) * as_nat c h0 r % prime_p256_order in 

	 let bufferU1 = nat_to_bytes_be 32 p0  in 
	 let bufferU2 = nat_to_bytes_be 32 p1 in 
	 let pointAtInfinity = (0, 0, 0) in
         let u1D, _ = montgomery_ladder_spec #c bufferU1 (pointAtInfinity, basePoint #P256) in
         let u2D, _ = montgomery_ladder_spec #c bufferU2 (pointAtInfinity, point_prime_to_coordinates c (as_seq h0 publicKeyPoint)) in
         let sumD = _point_add #c u1D u2D in
         let (xResult, yResult, zResult) = _norm #c sumD in
         state == not (Spec.P256.isPointAtInfinity (_norm #c sumD)) /\
         as_nat c h1 xBuffer == xResult
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


(*[@ (Comment "  This code is not side channel resistant")] *)

val ecdsa_verification_:
  #c: curve 
  ->  alg:hash_alg_ecdsa
  -> pubKey:lbuffer uint64 (size 8)
  -> r:lbuffer uint64 (size 4)
  -> s: lbuffer uint64 (size 4)
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #P256 alg}
  -> m:lbuffer uint8 mLen ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let pubKeyX = as_nat c h0 (gsub pubKey (size 0) (size 4)) in
      let pubKeyY = as_nat c h0 (gsub pubKey (size 4) (size 4)) in
      let r = as_nat c h0 r in
      let s = as_nat c h0 s in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile P256 alg (pubKeyX, pubKeyY) r s (v mLen) (as_seq h0 m))

let ecdsa_verification_ #c alg pubKey r s mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame();
  let tempBufferU64 = create (size 120) (u64 0) in
  let publicKeyBuffer = sub tempBufferU64 (size 0) (size 12) in
  let hashAsFelem = sub tempBufferU64 (size 12) (size 4) in
  let tempBuffer = sub tempBufferU64 (size 16) (size 100) in
  let xBuffer = sub tempBufferU64 (size 116) (size 4) in

  bufferToJac #c pubKey publicKeyBuffer;
  let publicKeyCorrect = verifyQValidCurvePoint #c publicKeyBuffer tempBuffer in
  if publicKeyCorrect = false then
    begin
    pop_frame();
    false
    end
  else
    let step1 = ecdsa_verification_step1 #c r s in
    if step1 = false then
      begin
      pop_frame();
      false
      end
    else
      let state = ecdsa_verification_core #c alg publicKeyBuffer hashAsFelem r s mLen m xBuffer tempBuffer in
      if state = false then
        begin
        pop_frame();
        false
        end
      else
        begin
        let result = compare_felem_bool #c xBuffer r in
        pop_frame();
        result
        end


inline_for_extraction
val ecdsa_verification:
  c: curve 
  -> alg:hash_alg_ecdsa
  -> pubKey:lbuffer uint8 (size 64)
  -> r:lbuffer uint8 (size 32)
  -> s:lbuffer uint8 (size 32)
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #P256 alg}
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
      result == Spec.ECDSA.ecdsa_verification_agile P256 alg (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m))

let ecdsa_verification c alg pubKey r s mLen m =
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
      
    toUint64ChangeEndian #c pubKeyX publicKeyFelemX;
    toUint64ChangeEndian #c pubKeyY publicKeyFelemY;
   
    toUint64ChangeEndian #c r rAsFelem;
    toUint64ChangeEndian #c s sAsFelem;

  let h1 = ST.get() in 
      lemma_core_0 c publicKeyFelemX h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);  
      lemma_core_0 c publicKeyFelemY h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY);

      lemma_core_0 c rAsFelem h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 r);
      lemma_core_0 c sAsFelem h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 s);

    let result = ecdsa_verification_ #c alg publicKeyAsFelem rAsFelem sAsFelem mLen m in 
    pop_frame();

    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 r));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 r);
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 s));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 s);

  result
