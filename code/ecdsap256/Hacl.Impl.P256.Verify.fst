module Hacl.Impl.P256.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.PointMul

open Hacl.Hash.SHA2
open Spec.Hash.Definitions

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication
module PS = Hacl.Impl.P256.Sign
module QI = Hacl.Impl.P256.Qinv

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
val ecdsa_verification_step4: u1:felem -> u2:felem -> r:felem -> s:felem -> z:felem -> Stack unit
  (requires fun h ->
    live h r /\ live h s /\ live h z /\ live h u1 /\ live h u2 /\
    disjoint u1 u2 /\ disjoint u1 z /\ disjoint u1 r /\ disjoint u1 s /\
    disjoint u2 z /\ disjoint u2 r /\ disjoint u2 s /\
    as_nat h s < S.order /\ as_nat h z < S.order /\ as_nat h r < S.order)
  (ensures fun h0 _ h1 -> modifies (loc u1 |+| loc u2) h0 h1 /\
    as_nat h1 u1 == S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 z % S.order /\
    as_nat h1 u2 == S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 r % S.order)

let ecdsa_verification_step4 u1 u2 r s z =
  push_frame ();
  let inverseS = create_felem () in

  fromDomainImpl s inverseS;
  QI.qinv inverseS inverseS;
  QI.multPowerPartial s inverseS z u1;
  QI.multPowerPartial s inverseS r u2;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_step5: x:felem -> pk:point -> u1:felem -> u2:felem -> Stack bool
  (requires fun h ->
    live h x /\ live h pk /\ live h u1 /\ live h u2 /\
    disjoint x u1 /\ disjoint x u2 /\ disjoint x pk /\
    disjoint pk u1 /\ disjoint pk u2 /\
    point_inv h pk /\ as_nat h u1 < pow2 256 /\ as_nat h u2 < pow2 256)
  (ensures fun h0 state h1 -> modifies (loc x |+| loc pk) h0 h1 /\
    as_nat h1 x < S.prime /\
   (let sumD = S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2) (as_point_nat h0 pk) in
    let res = S.norm_jacob_point sumD in
    let (res_x, _, _) = res in
    state == not (S.is_point_at_inf res) /\
    as_nat h1 x == res_x % S.order))

let ecdsa_verification_step5 x pk u1 u2 =
  push_frame ();
  let pointSum = create_point () in
  point_mul_double_g pointSum u1 u2 pk;
  norm_jacob_point pointSum pointSum;
  let is_res_point_at_inf = is_point_at_inf_vartime pointSum in
  let res_x = getx pointSum in
  copy x res_x;
  qmod_short x x;
  pop_frame ();
  not is_res_point_at_inf


inline_for_extraction
val ecdsa_verification_core:
    alg:S.hash_alg_ecdsa
  -> pk:point
  -> z:felem
  -> r:felem
  -> s:felem
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> x:felem ->
  Stack bool
  (requires fun h ->
    live h pk /\ live h z /\ live h r /\ live h s /\ live h msg /\ live h x /\
    disjoint pk r /\ disjoint pk s /\ disjoint pk msg /\ disjoint z r /\
    disjoint z s /\ disjoint z msg /\ disjoint x r /\ disjoint x s /\
    disjoint x msg /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pk; loc z; loc x] /\
    as_nat h s < S.order /\ as_nat h r < S.order /\
    point_inv h pk)
  (ensures fun h0 state h1 -> modifies (loc pk |+| loc z |+| loc x) h0 h1 /\
    (let hashM = S.hash_ecdsa alg (v msg_len) (as_seq h0 msg) in
    let z = BSeq.nat_from_bytes_be (LSeq.sub hashM 0 32) % S.order in
    let u1 = S.pow (as_nat h0 s) (S.order - 2) * z % S.order in
    let u2 = S.pow (as_nat h0 s) (S.order - 2) * as_nat h0 r % S.order in
    let sumD = S.point_mul_double_g u1 u2 (as_point_nat h0 pk) in
    let (res_x, _, _) = S.norm_jacob_point sumD in
    state == not (S.is_point_at_inf (S.norm_jacob_point sumD)) /\
    as_nat h1 x == res_x % S.order))

let ecdsa_verification_core alg pk z r s msg_len msg x =
  push_frame ();
  let u1 = create_felem () in
  let u2 = create_felem () in
  PS.msg_as_felem alg msg_len msg z;
  ecdsa_verification_step4 u1 u2 r s z;
  let r = ecdsa_verification_step5 x pk u1 u2 in
  pop_frame ();
  r


val ecdsa_verification_:
    alg:S.hash_alg_ecdsa
  -> public_key:lbuffer uint8 64ul
  -> r_q:felem
  -> s_q:felem
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h r_q /\ live h s_q /\ live h msg)
  (ensures fun h0 res h1 -> modifies0 h0 h1)
    //res == S.ecdsa_verification_agile alg (as_seq h0 pubKey) r s (v mLen) (as_seq h0 m))

let ecdsa_verification_ alg public_key r_q s_q msg_len msg =
  push_frame ();
  let z = create_felem () in
  let x = create_felem () in
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
      let state = ecdsa_verification_core alg pk z r_q s_q msg_len msg x in
      if state = false then
        begin
        pop_frame ();
        false
        end
      else
        begin
        let res = bn_is_eq_vartime4 x r_q in
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
