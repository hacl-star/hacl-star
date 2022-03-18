module Hacl.Impl.ECDSA.Verification

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

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

open Hacl.Impl.EC.PointAddC
open Hacl.Impl.EC.LowLevel.RawCmp

open Hacl.Hash.SHA2

open Hacl.Impl.P256.Signature.Common
open Lib.ByteSequence

open Hacl.Impl.EC.Intro

open Hacl.Impl.EC.Setup

open FStar.Mul
open Hacl.Impl.EC.Masking



#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0"


inline_for_extraction noextract
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


inline_for_extraction noextract
val ecdsa_verification_step4: #c: curve 
  -> bufferU1: scalar_t #MUT #c
  -> bufferU2: scalar_t #MUT #c
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
    fromForm #c u1 bufferU1;
    fromForm #c u2 bufferU2;
  let h2 = ST.get() in
  pop_frame()


let getU1U2 (#c: curve) (points: (lbuffer uint64 (getCoordinateLenU64 c *! 6ul))) = 
  gsub points (size 0) (getCoordinateLenU64 c *! 3ul), 
  gsub points (getCoordinateLenU64 c *! 3ul) (getCoordinateLenU64 c *! 3ul)


val point_mult0_is_infinity: #c: curve -> p: point_nat_prime #c -> Lemma (point_mult #c 0 p == pointAtInfinity)

let point_mult0_is_infinity #c p = Spec.ECC.point_mult_0 p 0


inline_for_extraction noextract
val ecdsa_verification_step5_0: #c: curve 
  -> #l: ladder 
  -> points:lbuffer uint64 (getCoordinateLenU64 c *! 6ul)
  -> pubKeyAsPoint: point c
  -> u1: scalar_t #MUT #c
  -> u2: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 c *! 20ul) ->
  Stack unit
  (requires fun h ->
    live h points)
  (ensures fun h0 _ h1 -> modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc points) h0 h1)
    

let ecdsa_verification_step5_0 #c #l points pubKeyAsPoint u1 u2 tempBuffer =
    let h0 = ST.get() in 
    let pointU1G = sub points (size 0) (getCoordinateLenU64 c *! 3ul) in
    let pointU2Q = sub points (getCoordinateLenU64 c *! 3ul) (getCoordinateLenU64 c *! 3ul) in
  secretToPublicWithoutNorm #c #l pointU1G u1 tempBuffer; 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint; 
  scalarMultiplicationWithoutNorm #c #l pubKeyAsPoint pointU2Q u2 tempBuffer;
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
val ecdsa_verification_step5_1: #c: curve -> points:lbuffer uint64 (getCoordinateLenU64 c *! 6ul) 
  -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> live h points /\ live h result /\ live h tempBuffer /\ 
    disjoint points tempBuffer /\ disjoint points result /\ disjoint result tempBuffer /\ (
    let p, q = getU1U2 #c points in 
    point_eval c h p /\ point_eval c h q /\ ~ (isPointAtInfinity #Jacobian (point_as_nat c h p)) /\ 
     ~ (isPointAtInfinity #Jacobian (point_as_nat c h q))))
  (ensures fun h0 r h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p, q = getU1U2 #c points in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
    point_as_nat c h1 result == _norm (pointAdd #c pD qD)))

let ecdsa_verification_step5_1 #c points result tempBuffer = 
  let tempBuffer17 = sub tempBuffer (size 0) (getCoordinateLenU64 c *! 17ul) in 
  let p = sub points (size 0) (getCoordinateLenU64 c *! 3ul) in 
  let q = sub points (getCoordinateLenU64 c *! 3ul) (getCoordinateLenU64 c *! 3ul) in 
  Hacl.Impl.EC.PointAddC.point_add_c p q result tempBuffer17;
  norm result result tempBuffer17


inline_for_extraction noextract
val ecdsa_verification_step5_2: #c: curve 
  -> #l: ladder 
  -> result: point c
  -> pubKeyAsPoint: point c
  -> u1: scalar_t #MUT #c
  -> u2: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h ->
    live h result /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\
    disjoint pubKeyAsPoint u1 /\ disjoint pubKeyAsPoint u2 /\ disjoint tempBuffer u1 /\ disjoint tempBuffer u2 /\
    disjoint pubKeyAsPoint tempBuffer /\ disjoint result tempBuffer /\ 
    point_eval c h pubKeyAsPoint /\ ~ (isPointAtInfinity #Jacobian (point_as_nat c h pubKeyAsPoint)))
  (ensures fun h0 _ h1 -> modifies (loc pubKeyAsPoint |+| loc result |+| loc tempBuffer) h0 h1 /\
    point_eval c h1 result /\ (
    point_mult0_is_infinity (basePoint #c); point_mult0_is_infinity (point_as_nat c h0 pubKeyAsPoint);
    let u1D, _ = montgomery_ladder_spec_left #c (as_seq h0 u1) (pointAtInfinity, basePoint #c) in
    let u2D, _ = montgomery_ladder_spec_left #c (as_seq h0 u2) (pointAtInfinity, point_as_nat c h0 pubKeyAsPoint) in
    point_as_nat c h1 result == _norm (pointAdd #c u1D u2D)))


let ecdsa_verification_step5_2 #c #l result pubKeyAsPoint u1 u2 tempBuffer =
    let h0 = ST.get() in 
  push_frame(); 
    let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let points = create (len *! 6ul) (u64 0) in 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint;
  ecdsa_verification_step5_0 #c #l points pubKeyAsPoint u1 u2 tempBuffer; 
    let h2 = ST.get() in 
      assume(
	let p, q = getU1U2 #c points in 
	~ (isPointAtInfinity #Jacobian (point_as_nat c h2 p)) /\ 
	~ (isPointAtInfinity #Jacobian (point_as_nat c h2 q)));
  ecdsa_verification_step5_1 points result tempBuffer;

    let h3 = ST.get() in 
  pop_frame();
    let h4 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 result


inline_for_extraction noextract
val ecdsa_verification_step5: #c: curve 
  -> #l: ladder
  -> x: felem c
  -> pubKeyAsPoint: point c
  -> u1: scalar_t #MUT #c
  -> u2: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack bool
  (requires fun h ->
    live h x /\ live h pubKeyAsPoint)
  (ensures fun h0 isPointAtInfinityState h1 -> modifies (loc pubKeyAsPoint |+| loc tempBuffer |+| loc x) h0 h1)
    

let ecdsa_verification_step5 #c #l x pubKeyAsPoint u1 u2 tempBuffer =
  let h0 = ST.get() in 
    push_frame();
        let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let result = create (len *! size 3) (u64 0) in
  let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint;
  ecdsa_verification_step5_2 #c #l result pubKeyAsPoint u1 u2 tempBuffer;
  let resultIsPAI = isPointAtInfinity_public #c result in
  let xCoordinateSum = sub result (size 0) (getCoordinateLenU64 c) in
  copy x xCoordinateSum;
  reduction_prime_2prime_order x x;
  pop_frame();
  not resultIsPAI


inline_for_extraction
val ecdsa_verification_step45: #c: curve 
  -> #l: ladder 
  -> u1: scalar_t #MUT #c
  -> u2: scalar_t #MUT #c
  -> r: felem c
  -> s: felem c
  -> hash: felem c 
  -> x: felem c
  -> pubKeyAsPoint: point c  
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack bool
  (requires fun h -> (
    let order = getOrder #c in 
    live h r /\ live h s /\ live h hash /\ live h u1 /\ live h u2 /\ live h x /\ live h pubKeyAsPoint /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc r; loc s; loc u1; loc u2; loc hash; loc x; loc pubKeyAsPoint; loc tempBuffer] /\
    point_eval c h pubKeyAsPoint /\ 
    as_nat c h s < order /\ as_nat c h hash < order /\ as_nat c h r < order))
  (ensures fun h0 isPAI h1 -> True)


let ecdsa_verification_step45 #c #l u1 u2 r s hash x pubKeyAsPoint tempBuffer = 
    let h0 = ST.get() in 
  ecdsa_verification_step4 u1 u2 r s hash;
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint;
  ecdsa_verification_step5 #c #l x pubKeyAsPoint u1 u2 tempBuffer



inline_for_extraction
val ecdsa_verification_core_ :#c: curve 
  -> #l: ladder 
  -> alg: hash_alg_ecdsa
  -> pubKeyAsPoint: point c
  -> hashAsFelem: felem c
  -> r: felem c
  -> s: felem c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg} 
  -> m: lbuffer uint8 mLen
  -> x:felem c
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack bool
  (requires fun h ->
    let order = getOrder #c in (
    live h pubKeyAsPoint /\ live h hashAsFelem /\ live h r /\ live h s /\ live h m /\ live h x /\ live h tempBuffer /\
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32 /\
    as_nat c h s < order /\  as_nat c h r < order /\
    
    LowStar.Monotonic.Buffer.all_disjoint [loc r; loc s; loc hashAsFelem; loc x; loc pubKeyAsPoint; loc tempBuffer] /\
    
    point_eval c h pubKeyAsPoint /\ ~ (isPointAtInfinity #Jacobian (point_as_nat c h pubKeyAsPoint))))
  (ensures fun h0 isPointAtInfinityState h1 -> 
    modifies (loc pubKeyAsPoint |+| loc hashAsFelem |+| loc x |+| loc tempBuffer) h0 h1 /\ (
    let order = getOrder #c in 
    
    let message = hashSpec c alg (v mLen) (as_seq h0 m) % order in 
    let p0 = pow (as_nat c h0 s) (order - 2) * message % order in 
    let p1 = pow (as_nat c h0 s) (order - 2) * as_nat c h0 r % order in 
    let u1 = nat_to_bytes_be (v (getCoordinateLenU c)) p0 in 
    let u2 = nat_to_bytes_be (v (getCoordinateLenU c)) p1 in

    point_mult0_is_infinity (basePoint #c); point_mult0_is_infinity (point_as_nat c h0 pubKeyAsPoint);
    
    let u1D, _ = montgomery_ladder_spec_left #c u1 (pointAtInfinity, basePoint #c) in
    let u2D, _ = montgomery_ladder_spec_left #c u2 (pointAtInfinity, point_as_nat c h0 pubKeyAsPoint) in
    let normSum = _norm (pointAdd #c u1D u2D) in 
    let xN, yN, zN = normSum in 
    as_nat c h1 x == xN % order /\
    isPointAtInfinityState = not (isPointAtInfinity #Jacobian normSum)))


let ecdsa_verification_core_ #c #l alg pubKeyAsPoint hashAsFelem r s mLen m x tempBuffer =
    assert_norm (pow2 32 < pow2 61 - 1);
    assert_norm (pow2 32 < pow2 125);
    let h0 = ST.get() in 
  push_frame();
      let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let tempBufferU8 = create (size 2 *! len) (u8 0) in
    let u1 = sub tempBufferU8 (size 0) (getCoordinateLenU c) in
    let u2 = sub tempBufferU8 (getCoordinateLenU c) (getCoordinateLenU c) in
  ecdsa_verification_step23 alg mLen m hashAsFelem;
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKeyAsPoint;
  let r = ecdsa_verification_step45 #c #l u1 u2 r s hashAsFelem x pubKeyAsPoint tempBuffer in
  pop_frame();
  r

inline_for_extraction
[@ (Comment "  This code is not side channel resistant")] 
val ecdsa_verification_core: #c: curve 
  -> #l: ladder 
  -> alg: hash_alg_ecdsa
  -> pubKey: pointAffine c
  -> r: felem c
  -> s: felem c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen
  -> publicKeyBuffer: point c
  -> hashAsFelem: felem c
  -> x: felem c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack bool
  (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m /\ live h publicKeyBuffer /\ live h hashAsFelem /\ 
    live h x /\ live h tempBuffer /\
    felem_eval c h (getXAff pubKey) /\ felem_eval c h (getYAff pubKey) /\ point_eval c h publicKeyBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc r; loc s; loc m; loc hashAsFelem; loc x; loc pubKey; loc publicKeyBuffer; loc tempBuffer] /\
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32 /\ (
    let order = getOrder #c in 
    as_nat c h s < order /\  as_nat c h r < order))
  (ensures fun h0 result h1 -> modifies (loc publicKeyBuffer |+| loc tempBuffer |+| loc hashAsFelem |+| loc x) h0 h1 /\ (
    let pubKeyX = as_nat c h0 (getXAff pubKey)  in
    let pubKeyY = as_nat c h0 (getYAff pubKey) in
    let r = as_nat c h0 r in
    let s = as_nat c h0 s in
    result == Spec.ECDSA.ecdsa_verification c alg (pubKeyX, pubKeyY) r s (v mLen) (as_seq h0 m)))



let ecdsa_verification_core #c #l alg pubKey r s mLen m publicKeyBuffer hashAsFelem x tempBuffer = 
  bufferToJac #c pubKey publicKeyBuffer; 
    let h0 = ST.get() in 
  let publicKeyCorrect = verifyQValidCurvePoint_public #c #l publicKeyBuffer tempBuffer in
  if publicKeyCorrect = false then false
  else 
    let step1 = ecdsa_verification_step1 #c r s in
    if step1 = false then false
    else
	let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 publicKeyBuffer; 
      let state = ecdsa_verification_core_ #c #l alg publicKeyBuffer hashAsFelem r s mLen m x tempBuffer in 
      if state = false then false
      else cmp_felem_felem_bool #c x r


inline_for_extraction
val ecdsa_verification_: #c: curve 
  -> #l: ladder
  -> alg: hash_alg_ecdsa
  -> pubKey: pointAffine c
  -> r: felem c
  -> s: felem c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen ->
  Stack bool
  (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m /\ 
    felem_eval c h (getXAff pubKey) /\ felem_eval c h (getYAff pubKey) /\
    LowStar.Monotonic.Buffer.all_disjoint [loc r; loc s; loc m; loc pubKey] /\
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32 /\ (
    let order = getOrder #c in 
    as_nat c h s < order /\  as_nat c h r < order))
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\ (
    let pubKeyX = as_nat c h0 (getXAff pubKey)  in
    let pubKeyY = as_nat c h0 (getYAff pubKey) in
    let r = as_nat c h0 r in
    let s = as_nat c h0 s in
    result == Spec.ECDSA.ecdsa_verification c alg (pubKeyX, pubKeyY) r s (v mLen) (as_seq h0 m)))

let ecdsa_verification_ #c #l alg pubKey r s mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (len *! size 20) (u64 0) in 
    let hashAsFelem = create len (u64 0) in
    let x = create len (u64 0) in 
    let publicKeyBuffer = create (len *! size 3) (u64 0) in 
    
    let h1 = ST.get() in 
    lemma_create_zero_buffer #U64 (3 * v len) c;
    Hacl.Impl.EC.DH.lemma_zero_point_zero_coordinates c h1 publicKeyBuffer;

  let r = ecdsa_verification_core #c #l alg pubKey r s mLen m publicKeyBuffer hashAsFelem x tempBuffer in
  pop_frame();
    let h2 = ST.get() in 
    assert(modifies0 h0 h2);
  r


inline_for_extraction
val ecdsa_verification_to_form: #c: curve 
  -> #l: ladder 
  -> pubKey: pointAffine8 c
  -> pubKeyBuffer: lbuffer uint64 (size 2 *! getCoordinateLenU64 c) 
  -> r: lbuffer uint8 (getCoordinateLenU c)
  -> s: lbuffer uint8 (getCoordinateLenU c)
  -> rBuffer: felem c -> sBuffer: felem c -> 
  Stack unit 
  (requires fun h -> live h pubKey /\ live h pubKeyBuffer /\ live h r /\ live h s /\ live h rBuffer /\ live h sBuffer /\
    disjoint pubKey pubKeyBuffer /\ disjoint r rBuffer /\ disjoint s sBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc pubKeyBuffer; loc r; loc s; loc rBuffer; loc sBuffer])
  (ensures fun h0 _ h1 -> modifies (loc pubKeyBuffer |+| loc rBuffer |+| loc sBuffer) h0 h1 /\
    as_nat c h1 rBuffer == nat_from_bytes_be (as_seq h0 r) /\
    as_nat c h1 sBuffer == nat_from_bytes_be (as_seq h0 s) /\ (
    let len = getCoordinateLenU64 c in 
    let pubKeyX = gsub pubKey (size 0) (getCoordinateLenU c) in
    let pubKeyY = gsub pubKey (getCoordinateLenU c) (getCoordinateLenU c) in 

    let pFX = gsub pubKeyBuffer (size 0) len in 
    let pFY = gsub pubKeyBuffer len len in 

    as_nat c h1 pFX == nat_from_bytes_be (as_seq h0 pubKeyX) /\
    as_nat c h1 pFY == nat_from_bytes_be (as_seq h0 pubKeyY)))


let ecdsa_verification_to_form #c #l pubKey pubKeyBuffer r s rBuffer sBuffer = 
  let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 

  let publicKeyFelemX = sub pubKeyBuffer (size 0) len in 
  let publicKeyFelemY = sub pubKeyBuffer len len in 
  
  let pubKeyX = sub pubKey (size 0) (getCoordinateLenU c) in
  let pubKeyY = sub pubKey (getCoordinateLenU c) (getCoordinateLenU c) in 
    
  toUint64ChangeEndian #c pubKeyX publicKeyFelemX;
  toUint64ChangeEndian #c pubKeyY publicKeyFelemY;
   
  toUint64ChangeEndian #c r rBuffer;
  toUint64ChangeEndian #c s sBuffer
  


inline_for_extraction
val ecdsa_verification: #c: curve 
  -> #l: ladder 
  -> alg: hash_alg_ecdsa
  -> pubKey: pointAffine8 c
  -> r: lbuffer uint8 (getCoordinateLenU c)
  -> s: lbuffer uint8 (getCoordinateLenU c)
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen ->
  Stack bool
  (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m /\ (
    match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32 /\
    nat_from_bytes_be (as_seq h r) < getOrder #c /\ nat_from_bytes_be (as_seq h s) < getOrder #c /\ (
    let pubKeyX = gsub pubKey (size 0) (getCoordinateLenU c) in
    let pubKeyY = gsub pubKey (getCoordinateLenU c) (getCoordinateLenU c) in 
    nat_from_bytes_be (as_seq h pubKeyX) < getPrime c /\ nat_from_bytes_be (as_seq h pubKeyY) < getPrime c) /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc r; loc s])
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\ (
    let pubKeyX = gsub pubKey (size 0) (getCoordinateLenU c) in
    let pubKeyY = gsub pubKey (getCoordinateLenU c) (getCoordinateLenU c) in 

    let pFX = nat_from_bytes_be (as_seq h0 pubKeyX) in 
    let pFY = nat_from_bytes_be (as_seq h0 pubKeyY) in 
    
    let r = nat_from_bytes_be (as_seq h0 r) in
    let s = nat_from_bytes_be (as_seq h0 s) in
    result == Spec.ECDSA.ecdsa_verification c alg (pFX, pFY) r s  (v mLen) (as_seq h0 m)))


let ecdsa_verification #c #l alg pubKey r s mLen m =
  push_frame();
  let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 4 *! len) (u64 0) in 
      let publicKeyAsFelem = sub tempBuffer (size 0) (size 2 *! len) in
      let rAsFelem = sub tempBuffer (size 2 *! len) len in 
      let sAsFelem = sub tempBuffer (size 3 *! len) len in 
  ecdsa_verification_to_form #c #l pubKey publicKeyAsFelem r s rAsFelem sAsFelem;
  let result = ecdsa_verification_ #c #l alg publicKeyAsFelem rAsFelem sAsFelem mLen m in 
  pop_frame();
  result
