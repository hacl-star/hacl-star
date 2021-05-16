module Hacl.Impl.ECDSA.Verification

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.EC.Lemmas

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.Core
open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.ECDSA.LowLevel
open Hacl.Impl.ECDSA.MM.Exponent

open Spec.ECDSA
open Spec.ECC
open Hacl.Spec.EC.Definition
open Spec.ECC.Curves

open Hacl.Impl.EC.PointAdd
open Hacl.Impl.EC.LowLevel.RawCmp

open Hacl.Hash.SHA2

open Hacl.Impl.P256.Signature.Common
open Lib.ByteSequence

open Hacl.Impl.EC.Intro

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open Hacl.Impl.EC.Setup

open FStar.Mul
open Hacl.Impl.EC.Masking



#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0"


[@ (Comment "  This code is not side channel resistant")] 
val isMoreThanZeroLessThanOrderMinusOne: #c: curve -> f: felem c -> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r = (as_nat c h0 f > 0 && as_nat c h0 f < getOrder #c))

let isMoreThanZeroLessThanOrderMinusOne #c f =
  push_frame();
  let len = getCoordinateLenU64 c in 
  let tempBuffer = create len (u64 0) in
  let carry = sub_bn_order #c f tempBuffer in
  let less = eq_u64_nCT carry (u64 1) in
  let more = isZero_uint64_nCT f in
  let result = less && not more in
  pop_frame();
  result


inline_for_extraction noextract
val ecdsa_verification_step1: #c: curve -> r: lbuffer uint64 (getCoordinateLenU64 c) 
  -> s:lbuffer uint64 (getCoordinateLenU64 c) -> Stack bool
  (requires fun h -> live h r /\ live h s)
  (ensures  fun h0 result h1 ->
    modifies0 h0 h1 /\
    result == checkCoordinates #c (as_nat c h0 r) (as_nat c h0 s))

let ecdsa_verification_step1 #c r s =
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne #c r in
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne #c s in
  isRCorrect && isSCorrect


inline_for_extraction
val ecdsa_verification_step23:   #c: curve 
  -> alg:hash_alg_ecdsa
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg} 
  -> m: lbuffer uint8 mLen -> result: felem c -> Stack unit
  (requires fun h -> live h m /\ live h result /\ 
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let message = hashSpec c alg (v mLen) (as_seq h0 m) in 
    as_nat c h1 result == message % getOrder #c /\
    as_nat c h1 result < getOrder #c))


let ecdsa_verification_step23 #c alg mLen m result = 
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame(); 
  let sz_hash: FStar.UInt32.t = match alg with |NoHash -> mLen |Hash a -> hash_len a in

  let len: FStar.UInt32.t  = sz_hash +! getCoordinateLenU c in 
  let mHash = create len (u8 0) in 
    let h0 = ST.get() in 
    let mHashHPart = sub mHash (size 0) sz_hash in 
    let mHashRPart = sub mHash (size 0) (getCoordinateLenU c) in 
    let mHashHPartLeft = sub mHash sz_hash (getCoordinateLenU c) in 
    let mHashLeft = sub mHash (getCoordinateLenU c) sz_hash in 
    
  begin
  match alg with 
    |NoHash -> copy mHashHPart m 
    |Hash a -> match a with 
      |SHA2_256 -> hash_256 m mLen mHashHPart
      |SHA2_384 -> hash_384 m mLen mHashHPart
      |SHA2_512 -> hash_512 m mLen mHashHPart 
  end;
    let h1 = ST.get() in 
  toUint64ChangeEndian #c mHashRPart result;
    let h2 = ST.get() in 
  reduction_prime_2prime_order result result;
  pop_frame();
      let h3 = ST.get() in 

  lemma_create_zero_buffer #U8 (v len) c;
  Hacl.Impl.ECDSA.Signature.ecdsa_signature_step12_lemma c sz_hash (getCoordinateLenU c) h0 h1 mHash mHashHPart (as_seq h1 mHashHPart);

  lemma_lseq_nat_from_bytes (as_seq h1 mHashRPart);
  lemma_nat_from_to_intseq_le_preserves_value #U8 #SEC (getCoordinateLen c) (as_seq h1 mHashRPart);
  lemma_lseq_nat_from_bytes (as_seq h2 result)


#push-options "--ifuel 1"

inline_for_extraction noextract
val ecdsa_verification_step4: #c: curve 
  -> bufferU1: lbuffer uint8 (getCoordinateLenU c)
  -> bufferU2: lbuffer uint8 (getCoordinateLenU c)
  -> r: felem c
  -> s: felem c
  -> hash: felem c ->
  Stack unit
  (requires fun h -> (
    let order = getOrder #c in 
    live h r /\ live h s /\ live h hash /\ live h bufferU1 /\ live h bufferU2 /\
    disjoint bufferU1 bufferU2 /\ disjoint bufferU1 hash /\ disjoint bufferU1 r /\ disjoint bufferU1 s /\
    disjoint bufferU2 hash /\ disjoint bufferU2 r /\ disjoint bufferU2 s /\
    as_nat c h s < order /\ as_nat c h hash < order /\ as_nat c h r < order))
  (ensures fun h0 _ h1 -> modifies (loc bufferU1 |+| loc bufferU2) h0 h1 /\ (
    let order = getOrder #c in 
    let p0 = pow (as_nat c h0 s) (order - 2) * as_nat c h0 hash % order in 
    let p1 = pow (as_nat c h0 s) (order - 2) * as_nat c h0 r % order in 
    as_seq h1 bufferU1 == nat_to_bytes_be (v (getCoordinateLenU c)) p0 /\ 
    as_seq h1 bufferU2 == nat_to_bytes_be (v (getCoordinateLenU c)) p1))

let ecdsa_verification_step4 #c bufferU1 bufferU2 r s hash =
  push_frame();
  let h0 = ST.get() in
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 3 *! len) (u64 0) in
      let inverseS = sub tempBuffer (size 0) len in
      let u1 = sub tempBuffer len len in
      let u2 = sub tempBuffer (size 2 *! len) len in

    fromDomainImpl s inverseS;
    montgomery_ladder_exponent #c inverseS inverseS;
    multPowerPartial s inverseS hash u1;
    multPowerPartial s inverseS r u2;

  let h1 = ST.get() in 
    fromForm u1 bufferU1;
    fromForm u2 bufferU2;
  let h2 = ST.get() in
  pop_frame()


let getU1U2 (#c: curve) (points: (lbuffer uint64 (getCoordinateLenU64 c *! 6ul))) = 
  gsub points (size 0) (getCoordinateLenU64 c *! 3ul), 
  gsub points (getCoordinateLenU64 c *! 3ul) (getCoordinateLenU64 c *! 3ul)


val point_mult0_is_infinity: #c: curve -> p: point_nat_prime #c -> Lemma (point_mult #c 0 p == pointAtInfinity)

let point_mult0_is_infinity #c p = Spec.ECC.point_mult_0 p 0


inline_for_extraction noextract
val ecdsa_verification_step5_0: #c: curve 
  -> points:lbuffer uint64 (getCoordinateLenU64 c *! 6ul)
  -> pubKeyAsPoint: point c
  -> u1: scalar_t #MUT #c
  -> u2: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 c *! 20ul) ->
  Stack unit
  (requires fun h ->
    live h points /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\
    disjoint points u1 /\ disjoint points u2 /\ disjoint pubKeyAsPoint u1 /\ 
    disjoint pubKeyAsPoint u2 /\ disjoint tempBuffer u1 /\ disjoint tempBuffer u2 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc points; loc pubKeyAsPoint; loc tempBuffer] /\
    point_eval c h pubKeyAsPoint /\ ~ (isPointAtInfinity (point_as_nat c h pubKeyAsPoint)))
  (ensures fun h0 _ h1 -> modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc points) h0 h1 /\ (
    let pointU1G, pointU2Q = getU1U2 #c points in (point_eval c h1 pointU1G /\ point_eval c h1 pointU2Q /\ (
    let fromDomainPointU1 = fromDomainPoint #c #DH (point_as_nat c h1 pointU1G) in
    let fromDomainPointU2 = fromDomainPoint #c #DH (point_as_nat c h1 pointU2Q) in
      point_mult0_is_infinity (basePoint #c); point_mult0_is_infinity (point_as_nat c h0 pubKeyAsPoint);
    let u1D, _ = montgomery_ladder_spec_left #c (as_seq h0 u1) (pointAtInfinity, basePoint #c) in
    let u2D, _ = montgomery_ladder_spec_left #c (as_seq h0 u2) (pointAtInfinity, point_as_nat c h0 pubKeyAsPoint) in
    fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D))))
    

let ecdsa_verification_step5_0 #c points pubKeyAsPoint u1 u2 tempBuffer =
    let h0 = ST.get() in 
    let pointU1G = sub points (size 0) (getCoordinateLenU64 c *! 3ul) in
    let pointU2Q = sub points (getCoordinateLenU64 c *! 3ul) (getCoordinateLenU64 c *! 3ul) in
  secretToPublicWithoutNorm #c pointU1G u1 tempBuffer; 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint; 
  scalarMultiplicationWithoutNorm pubKeyAsPoint pointU2Q u2 tempBuffer;
    let h2 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 pointU1G


inline_for_extraction noextract
val compare_points_bool: #c: curve -> a: point c -> b: point c -> Stack bool
  (requires fun h -> live h a /\ live h b /\ point_eval c h a /\ point_eval c h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let xP, yP, zP = point_as_nat c h0 a in 
    let xQ, yQ, zQ = point_as_nat c h0 b in 
    r == ((xP = xQ) && (yP = yQ) && (zP = zQ))))

let compare_points_bool #c a b = 
  let len = getCoordinateLenU64 c in 
  let x0 = sub a (size 0) len in 
  let y0 = sub a len len in 
  let z0 = sub a (size 2 *! len) len in 

  let x1 = sub b (size 0) len in 
  let y1 = sub b len len in 
  let z1 = sub b (size 2 *! len) len in 

  let xEqual = cmp_felem_felem_bool #c x0 x1 in
  let yEqual = cmp_felem_felem_bool #c y0 y1 in 
  let zEqual = cmp_felem_felem_bool #c z0 z1 in 
  xEqual && yEqual && zEqual


inline_for_extraction noextract
val ecdsa_verification_step5_1: #c: curve -> points:lbuffer uint64 (size 24) -> Stack bool
  (requires fun h -> live h points /\
    as_nat c h (gsub points (size 0) (size 4)) < prime256 /\
    as_nat c h (gsub points (size 4) (size 4)) < prime256 /\
    as_nat c h (gsub points (size 8) (size 4)) < prime256 /\
    as_nat c h (gsub points (size 12) (size 4)) < prime256 /\
    as_nat c h (gsub points (size 16) (size 4)) < prime256 /\
    as_nat c h (gsub points (size 20) (size 4)) < prime256
  )
  (ensures fun h0 r h1 -> modifies0 h0 h1 (* /\ 
    (
      let pointU1G = gsub points (size 0) (size 12) in 
      let pointU2Q = gsub points (size 12) (size 12) in 
      r = (
  _norm (fromDomainPoint (point_prime_to_coordinates (as_seq h0 pointU1G))) =
  _norm (fromDomainPoint (point_prime_to_coordinates (as_seq h0 pointU2Q))))
    ) *)
  )

let ecdsa_verification_step5_1 #c points = 
  push_frame();
  
  let tmp = create (size 112) (u64 0) in 
  let tmpForNorm = sub tmp (size 0) (size 88) in 
  let result0Norm = sub tmp (size 88) (size 12) in 
  let result1Norm = sub tmp (size 100) (size 12) in 
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in 
  
  norm #c pointU1G result0Norm tmpForNorm;
  norm #c pointU2Q result1Norm tmpForNorm;
  let equalX = compare_points_bool #c result0Norm result1Norm in 

  pop_frame();
  equalX



inline_for_extraction noextract
val ecdsa_verification_step5_2:
  #c: curve ->
  (*m0: montgomery_ladder_mode ->
  m1: montgomery_ladder_mode -> *)
    pointSum: point c
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
      disjoint tempBuffer u2 (* /\
      LowStar.Monotonic.Buffer.all_disjoint [loc pointSum; loc pubKeyAsPoint; loc tempBuffer] /\
      point_x_as_nat h pubKeyAsPoint < prime256 /\
      point_y_as_nat h pubKeyAsPoint < prime256 /\
      point_z_as_nat h pubKeyAsPoint < prime256 *)
    )
    (ensures fun h0 _ h1 ->
      modifies (loc pointSum |+| loc tempBuffer |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat c h1 (gsub pointSum (size 0) (size 4)) < prime256 (* /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec_left (as_seq h0 u1) (pointAtInfinity, basePoint) in
        let u2D, _ = montgomery_ladder_spec_left (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
  let sumD = 
    if  _norm u1D =  _norm u2D
    then
      _point_double u1D
    else 
      _point_add u1D u2D in 
        let pointNorm = _norm sumD in
        let resultPoint =  point_prime_to_coordinates (as_seq h1 pointSum) in
        pointNorm == resultPoint
      ) *)
   )


let ecdsa_verification_step5_2 (* m0 m1 *) pointSum pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let points = create (size 24) (u64 0) in 
  let buff = sub tempBuffer (size 12) (size 88) in
  ecdsa_verification_step5_0 (*m0 m1 *) points pubKeyAsPoint u1 u2 tempBuffer;
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in 
(); (*
  let equalX = ecdsa_verification_step5_1 points in 
  begin
  if equalX then
    point_double pointU1G pointSum buff
  else  
    point_add pointU1G pointU2Q pointSum buff end;
  norm pointSum pointSum buff;  *)
  pop_frame()


inline_for_extraction noextract
val ecdsa_verification_step5: (*
  m0: montgomery_ladder_mode ->
  m1: montgomery_ladder_mode -> *)
 
  #c: curve 
  ->  x:felem c
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
      as_nat c h1 x < prime256 (*/\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = montgomery_ladder_spec_left (as_seq h0 u1) (pointAtInfinity, basePoint) in
        let u2D, _ = montgomery_ladder_spec_left (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in
        let sumD = 
    if  _norm u1D =  _norm u2D
    then
      _point_double u1D
    else 
      _point_add u1D u2D in 
        let pointNorm = _norm sumD in
        let (xResult, yResult, zResult) = pointNorm in
        state == not (Spec.ECC.isPointAtInfinity pointNorm) /\
        as_nat h1 x == xResult % prime_p256_order
    ) *)
  )

let ecdsa_verification_step5  #c (* m0 m1 *) x pubKeyAsPoint u1 u2 tempBuffer =
  push_frame();
  let pointSum = create (size 12) (u64 0) in
  ecdsa_verification_step5_2 (* m0 m1 *) pointSum pubKeyAsPoint u1 u2 tempBuffer;
  let resultIsPAI = isPointAtInfinityPublic #c pointSum in
  let xCoordinateSum = sub pointSum (size 0) (size 4) in
  copy x xCoordinateSum;
  reduction_prime_2prime_order x x;
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


let prime_p256_order = getOrder #P256

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
      (* as_nat c h s < prime_p256_order /\ as_nat c h r < prime_p256_order /\ *)
      point_x_as_nat c h publicKeyPoint < prime256 /\
      point_y_as_nat c h publicKeyPoint < prime256 /\
      point_z_as_nat c h publicKeyPoint < prime256
    )
    (ensures fun h0 state h1 ->
      modifies (loc publicKeyPoint |+| loc hashAsFelem |+| loc xBuffer |+| loc tempBuffer) h0 h1 (*/\
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
         let u1D, _ = montgomery_ladder_spec_left #c bufferU1 (pointAtInfinity, basePoint #P256) in
         let u2D, _ = montgomery_ladder_spec_left #c bufferU2 (pointAtInfinity, point_prime_to_coordinates c (as_seq h0 publicKeyPoint)) in
         let sumD = _point_add #c u1D u2D in
         let (xResult, yResult, zResult) = _norm #c sumD in
         state == not (Spec.ECC.isPointAtInfinity (_norm #c sumD)) /\
         as_nat c h1 xBuffer == xResult
      )*)
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

(*     changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 r));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 r);
    
    changeEndianLemma #c (uints_from_bytes_be (as_seq h1 s));
    uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 s); *)

  result
