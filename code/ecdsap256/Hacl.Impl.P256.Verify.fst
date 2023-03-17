module Hacl.Impl.P256.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum
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
module SM = Hacl.Spec.P256.MontgomeryMultiplication
module BSeq = Lib.ByteSequence
module PS = Hacl.Impl.P256.Sign

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: use variable time cmp with scalar
inline_for_extraction noextract
val are_r_and_s_valid: r:felem -> s:felem -> Stack bool
  (requires fun h -> live h r /\ live h s)
  (ensures  fun h0 res h1 -> modifies0 h0 h1 /\
    res ==
      (0 < as_nat h0 r && as_nat h0 r < S.order &&
       0 < as_nat h0 s && as_nat h0 s < S.order))

let are_r_and_s_valid r s =
  let is_r_valid = bn_is_lt_order_and_gt_zero_mask4 r in
  let is_s_valid = bn_is_lt_order_and_gt_zero_mask4 s in
  Hacl.Bignum.Base.unsafe_bool_of_limb is_r_valid &&
  Hacl.Bignum.Base.unsafe_bool_of_limb is_s_valid


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
      as_nat h s < S.order /\
      as_nat h hash < S.order /\
      as_nat h r < S.order
    )
    (ensures fun h0 _ h1 ->
      modifies (loc bufferU1 |+| loc bufferU2) h0 h1 /\
      (
	let p0 = S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 hash % S.order in
	let p1 = S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 r % S.order in
	as_seq h1 bufferU1 == BSeq.nat_to_bytes_be 32 p0 /\
	as_seq h1 bufferU2 == BSeq.nat_to_bytes_be 32 p1
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
    qinv inverseS inverseS;
    multPowerPartial s inverseS hash u1;
    multPowerPartial s inverseS r u2;

  let h1 = ST.get() in
    bn_to_bytes_be4 u1 bufferU1;
    bn_to_bytes_be4 u2 bufferU2;

  let h2 = ST.get() in
  pop_frame()



inline_for_extraction noextract
val ecdsa_verification_step5_0:
    points:lbuffer uint64 (size 24)
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32) ->
  Stack unit
    (requires fun h ->
      live h points /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\
      disjoint points u1 /\
      disjoint points u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint points pubKeyAsPoint /\
      point_x_as_nat h pubKeyAsPoint < S.prime /\
      point_y_as_nat h pubKeyAsPoint < S.prime /\
      point_z_as_nat h pubKeyAsPoint < S.prime
    )
  (ensures fun h0 _ h1 ->
    modifies (loc points) h0 h1 /\
    as_nat h1 (gsub points (size 0) (size 4)) < S.prime /\
    as_nat h1 (gsub points (size 4) (size 4)) < S.prime /\
    as_nat h1 (gsub points (size 8) (size 4)) < S.prime /\
    as_nat h1 (gsub points (size 12) (size 4)) < S.prime /\
    as_nat h1 (gsub points (size 16) (size 4)) < S.prime /\
    as_nat h1 (gsub points (size 20) (size 4)) < S.prime /\
    (
      let pointU1 = gsub points (size 0) (size 12) in
      let pointU2 = gsub points (size 12) (size 12) in

      let fromDomainPointU1 = SM.fromDomainPoint (as_point_nat h1 pointU1) in
      let fromDomainPointU2 = SM.fromDomainPoint (as_point_nat h1 pointU2) in
      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = S.montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, S.base_point) in
      let u2D, _ = S.montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, as_point_nat h0 pubKeyAsPoint) in
      fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D
    )
  )

let ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2 =
  push_frame ();
  let u1_q = create_felem () in
  let u2_q = create_felem () in
  bn_from_bytes_be4 u1 u1_q;
  bn_from_bytes_be4 u2 u2_q;
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in
  point_mul_g pointU1G u1_q;
  point_mul pointU2Q pubKeyAsPoint u2_q;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_step5_2:
    pointSum: point
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32) ->
  Stack unit
    (requires fun h ->
      live h pointSum /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\
      disjoint pointSum u1 /\
      disjoint pointSum u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint pubKeyAsPoint pointSum /\
      point_x_as_nat h pubKeyAsPoint < S.prime /\
      point_y_as_nat h pubKeyAsPoint < S.prime /\
      point_z_as_nat h pubKeyAsPoint < S.prime
    )
    (ensures fun h0 _ h1 ->
      modifies (loc pointSum |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat h1 (gsub pointSum (size 0) (size 4)) < S.prime /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = S.montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, S.base_point) in
        let u2D, _ = S.montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, as_point_nat h0 pubKeyAsPoint) in
	let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
        let pointNorm = S.norm_jacob_point sumD in
        let resultPoint =  as_point_nat h1 pointSum in
        pointNorm == resultPoint
      )
   )


let ecdsa_verification_step5_2 pointSum pubKeyAsPoint u1 u2 =
  push_frame();
  let points = create (size 24) (u64 0) in
  let buff = create (size 88) (u64 0) in
  ecdsa_verification_step5_0 points pubKeyAsPoint u1 u2;
  let pointU1G = sub points (size 0) (size 12) in
  let pointU2Q = sub points (size 12) (size 12) in

  let equalX = is_point_eq_vartime pointU1G pointU2Q in
  begin
  if equalX then
  	point_double pointU1G pointSum buff
  else
  	point_add pointU1G pointU2Q pointSum buff end;
  norm_jacob_point pointSum pointSum;
  pop_frame()


inline_for_extraction noextract
val ecdsa_verification_step5:
    x:felem
  -> pubKeyAsPoint: point
  -> u1: lbuffer uint8 (size 32)
  -> u2: lbuffer uint8 (size 32) ->
  Stack bool
    (requires fun h ->
      live h x /\ live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\
      disjoint x u1 /\
      disjoint x u2 /\
      disjoint pubKeyAsPoint u1 /\
      disjoint pubKeyAsPoint u2 /\
      disjoint x pubKeyAsPoint /\
      point_x_as_nat h pubKeyAsPoint < S.prime /\
      point_y_as_nat h pubKeyAsPoint < S.prime /\
      point_z_as_nat h pubKeyAsPoint < S.prime
    )
    (ensures fun h0 state h1 ->
      modifies (loc x |+| loc pubKeyAsPoint) h0 h1 /\
      as_nat h1 x < S.prime /\
      (
        let pointAtInfinity = (0, 0, 0) in
        let u1D, _ = S.montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, S.base_point) in
        let u2D, _ = S.montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, as_point_nat h0 pubKeyAsPoint) in
        let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
        let pointNorm = S.norm_jacob_point sumD in
        let (xResult, yResult, zResult) = pointNorm in
        state == not (S.is_point_at_inf pointNorm) /\
        as_nat h1 x == xResult % S.order
    )
  )

let ecdsa_verification_step5 x pubKeyAsPoint u1 u2 =
  push_frame();
  let pointSum = create (size 12) (u64 0) in
  ecdsa_verification_step5_2 pointSum pubKeyAsPoint u1 u2;
  let resultIsPAI = is_point_at_inf_vartime pointSum in
  let xCoordinateSum = sub pointSum (size 0) (size 4) in
  copy x xCoordinateSum;
  qmod_short x x;
  pop_frame();
  not resultIsPAI


inline_for_extraction
val ecdsa_verification_core:
  alg:S.hash_alg_ecdsa
  -> publicKeyPoint:point
  -> hashAsFelem:felem
  -> r:lbuffer uint64 (size 4)
  -> s:lbuffer uint64 (size 4)
  -> mLen:size_t{v mLen >= S.min_input_length alg}
  -> m:lbuffer uint8 mLen
  -> xBuffer:felem ->
  Stack bool
    (requires fun h ->
      live h publicKeyPoint /\ live h hashAsFelem /\ live h r /\ live h s /\ live h m /\ live h xBuffer /\
      disjoint publicKeyPoint r /\
      disjoint publicKeyPoint s /\
      disjoint publicKeyPoint m /\
      disjoint hashAsFelem r /\
      disjoint hashAsFelem s /\
      disjoint hashAsFelem m /\
      disjoint xBuffer r /\
      disjoint xBuffer s /\
      disjoint xBuffer m /\
      LowStar.Monotonic.Buffer.all_disjoint [loc publicKeyPoint; loc hashAsFelem; loc xBuffer] /\
      as_nat h s < S.order /\ as_nat h r < S.order /\
      point_x_as_nat h publicKeyPoint < S.prime /\
      point_y_as_nat h publicKeyPoint < S.prime /\
      point_z_as_nat h publicKeyPoint < S.prime
    )
    (ensures fun h0 state h1 ->
      modifies (loc publicKeyPoint |+| loc hashAsFelem |+| loc xBuffer) h0 h1 /\
       (
	 let hashM = S.hash_ecdsa alg (v mLen) (as_seq h0 m) in
	 let cutHashM = Lib.Sequence.sub hashM 0 32 in
	 let hashNat =  BSeq.nat_from_bytes_be cutHashM % S.order in

         let p0 = S.pow (as_nat h0 s) (S.order - 2) * hashNat % S.order in
	 let p1 = S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 r % S.order in

	 let bufferU1 = BSeq.nat_to_bytes_be 32 p0  in
	 let bufferU2 = BSeq.nat_to_bytes_be 32 p1 in
	 let pointAtInfinity = (0, 0, 0) in
         let u1D, _ = S.montgomery_ladder_spec bufferU1 (pointAtInfinity, S.base_point) in
         let u2D, _ = S.montgomery_ladder_spec bufferU2 (pointAtInfinity, as_point_nat h0 publicKeyPoint) in
          let sumD =
	  if  norm_jacob_point u1D = norm_jacob_point u2D
	  then
	    S.point_double u1D
	  else
	    S.point_add u1D u2D in
         let (xResult, yResult, zResult) = S.norm_jacob_point sumD in
         state == not (S.is_point_at_inf (S.norm_jacob_point sumD)) /\
         as_nat h1 xBuffer == xResult % S.order
      )
  )

let ecdsa_verification_core alg publicKeyBuffer hashAsFelem r s mLen m xBuffer =
  push_frame();
  let tempBufferU8 = create (size 64) (u8 0) in
  let bufferU1 = sub tempBufferU8 (size 0) (size 32) in
  let bufferU2 = sub tempBufferU8 (size 32) (size 32) in
  PS.msg_as_felem alg mLen m hashAsFelem;
  ecdsa_verification_step4  bufferU1 bufferU2 r s hashAsFelem;
  let r = ecdsa_verification_step5 xBuffer publicKeyBuffer bufferU1 bufferU2 in
  pop_frame();
  r


val ecdsa_verification_:
    alg:S.hash_alg_ecdsa
  -> public_key:lbuffer uint8 64ul
  -> r_q:lbuffer uint64 4ul
  -> s_q:lbuffer uint64 4ul
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h r_q /\ live h s_q /\ live h msg)
  (ensures fun h0 res h1 -> modifies0 h0 h1)
    //res == S.ecdsa_verification_agile alg (as_seq h0 pubKey) r s (v mLen) (as_seq h0 m))

let ecdsa_verification_ alg public_key r_q s_q msg_len msg =
  push_frame ();
  let hashAsFelem = create_felem () in
  let xBuffer = create_felem () in
  let pk = create_point () in

  let publicKeyCorrect = load_point_vartime pk public_key in
  if publicKeyCorrect = false then
    begin
    pop_frame ();
    false
    end
  else
    let step1 = are_r_and_s_valid r_q s_q in
    if step1 = false then
      begin
      pop_frame ();
      false
      end
    else
      let state = ecdsa_verification_core alg pk hashAsFelem r_q s_q msg_len msg xBuffer in
      if state = false then
        begin
        pop_frame ();
        false
        end
      else
        begin
        let res = bn_is_eq_vartime4 xBuffer r_q in
        pop_frame ();
        res
        end


inline_for_extraction
val ecdsa_verification:
    alg:S.hash_alg_ecdsa
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h msg)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verification_agile alg (as_seq h0 public_key)
      (as_seq h0 signature_r) (as_seq h0 signature_s) (v msg_len) (as_seq h0 msg))

let ecdsa_verification alg msg_len msg public_key signature_r signature_s =
  push_frame ();
  let r_q = create_felem () in
  let s_q = create_felem () in
  bn_from_bytes_be4 signature_r r_q;
  bn_from_bytes_be4 signature_s s_q;

  let res = ecdsa_verification_ alg public_key r_q s_q msg_len msg in
  pop_frame ();
  res
