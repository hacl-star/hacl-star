module Hacl.Impl.P256.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.PointMul

module BSeq = Lib.ByteSequence

module S = Spec.P256
module SL = Spec.P256.Lemmas
module SM = Hacl.Spec.P256.Montgomery
module QI = Hacl.Impl.P256.Qinv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

val qmul_mont: sinv:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h sinv /\ live h b /\ live h res /\
    disjoint sinv res /\ disjoint b res /\
    as_nat h sinv < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res = (as_nat h0 sinv * SM.from_qmont (as_nat h0 b) * SM.qmont_R_inv) % S.order)

[@CInline]
let qmul_mont sinv b res =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem () in
  from_qmont tmp b;
  let h1 = ST.get () in
  assert (as_nat h1 tmp == SM.from_qmont (as_nat h0 b));
  qmul res sinv tmp;
  let h2 = ST.get () in
  assert (as_nat h2 res = (as_nat h1 sinv * as_nat h1 tmp * SM.qmont_R_inv) % S.order);
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_get_u12: u1:felem -> u2:felem -> r:felem -> s:felem -> z:felem -> Stack unit
  (requires fun h ->
    live h r /\ live h s /\ live h z /\ live h u1 /\ live h u2 /\
    disjoint u1 u2 /\ disjoint u1 z /\ disjoint u1 r /\ disjoint u1 s /\
    disjoint u2 z /\ disjoint u2 r /\ disjoint u2 s /\
    as_nat h s < S.order /\ as_nat h z < S.order /\ as_nat h r < S.order)
  (ensures fun h0 _ h1 -> modifies (loc u1 |+| loc u2) h0 h1 /\
    (let sinv = S.qinv (as_nat h0 s) in
    as_nat h1 u1 == sinv * as_nat h0 z % S.order /\
    as_nat h1 u2 == sinv * as_nat h0 r % S.order))

let ecdsa_verification_get_u12 u1 u2 r s z =
  push_frame ();
  let h0 = ST.get () in
  let sinv = create_felem () in
  QI.qinv sinv s;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 sinv == S.qinv (qmont_as_nat h0 s));
  //assert (as_nat h2 sinv * SM.qmont_R_inv % S.order ==
    //S.qinv (as_nat h1 sinv * SM.qmont_R_inv % S.order));

  SM.qmont_inv_mul_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 z);
  SM.qmont_inv_mul_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 r);
  qmul_mont sinv z u1;
  qmul_mont sinv r u2;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verify_finv: p:point -> r:felem -> Stack bool
  (requires fun h ->
    live h p /\ live h r /\ disjoint p r /\
    point_inv h p /\ 0 < as_nat h r /\ as_nat h r < S.order)
    //not (S.is_point_at_inf (from_mont_point (as_point_nat h p))))
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (let (_X, _Y, _Z) = from_mont_point (as_point_nat h0 p) in
     b <==> (S.fmul _X (S.finv _Z) % S.order = as_nat h0 r)))

let ecdsa_verify_finv p r_q =
  push_frame ();
  let x = create_felem () in
  to_aff_point_x x p;
  qmod_short x x;
  let res = bn_is_eq_vartime4 x r_q in
  pop_frame ();
  res


inline_for_extraction noextract
val ecdsa_verification_cmpr: r:felem -> pk:point -> u1:felem -> u2:felem -> Stack bool
  (requires fun h ->
    live h r /\ live h pk /\ live h u1 /\ live h u2 /\
    disjoint r u1 /\ disjoint r u2 /\ disjoint r pk /\
    disjoint pk u1 /\ disjoint pk u2 /\
    point_inv h pk /\ as_nat h u1 < S.order /\ as_nat h u2 < S.order /\
    0 < as_nat h r /\ as_nat h r < S.order)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    (let _X, _Y, _Z = S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2)
      (from_mont_point (as_point_nat h0 pk)) in
    b <==> (if S.is_point_at_inf (_X, _Y, _Z) then false
      else S.fmul _X (S.finv _Z) % S.order = as_nat h0 r)))

let ecdsa_verification_cmpr r pk u1 u2 =
  push_frame ();
  let res = create_point () in
  let h0 = ST.get () in
  point_mul_double_g res u1 u2 pk;
  let h1 = ST.get () in
  assert (S.to_aff_point (from_mont_point (as_point_nat h1 res)) ==
    S.to_aff_point (S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2)
      (from_mont_point (as_point_nat h0 pk))));

  SL.lemma_aff_is_point_at_inf (from_mont_point (as_point_nat h1 res));
  SL.lemma_aff_is_point_at_inf
    (S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2) (from_mont_point (as_point_nat h0 pk)));

  let b =
    if is_point_at_inf_vartime res then false
    else ecdsa_verify_finv res r in
  pop_frame ();
  b


inline_for_extraction noextract
val load_signature (r_q s_q:felem) (sign_r sign_s:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h sign_r /\ live h sign_s /\ live h r_q /\ live h s_q /\
    disjoint r_q s_q /\ disjoint r_q sign_r /\ disjoint r_q sign_s /\
    disjoint s_q sign_r /\ disjoint s_q sign_s)
  (ensures fun h0 res h1 -> modifies (loc r_q |+| loc s_q) h0 h1 /\
   (let r_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_r) in
    let s_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_s) in
    as_nat h1 r_q = r_q_nat /\ as_nat h1 s_q = s_q_nat /\
    res == (0 < r_q_nat && r_q_nat < S.order && 0 < s_q_nat && s_q_nat < S.order)))

let load_signature r_q s_q sign_r sign_s =
  bn_from_bytes_be4 r_q sign_r;
  bn_from_bytes_be4 s_q sign_s;
  let is_r_valid = bn_is_lt_order_and_gt_zero_mask4 r_q in
  let is_s_valid = bn_is_lt_order_and_gt_zero_mask4 s_q in
  Hacl.Bignum.Base.unsafe_bool_of_limb is_r_valid &&
  Hacl.Bignum.Base.unsafe_bool_of_limb is_s_valid


val ecdsa_verify_msg_as_qelem:
    m_q:felem
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h m_q /\
    as_nat h m_q < S.order)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verify_msg_as_qelem (as_nat h0 m_q)
      (as_seq h0 public_key) (as_seq h0 signature_r) (as_seq h0 signature_s))

[@CInline]
let ecdsa_verify_msg_as_qelem m_q public_key signature_r signature_s =
  push_frame ();
  let tmp = create 28ul (u64 0) in
  let pk  = sub tmp 0ul 12ul in
  let r_q = sub tmp 12ul 4ul in
  let s_q = sub tmp 16ul 4ul in
  let u1  = sub tmp 20ul 4ul in
  let u2  = sub tmp 24ul 4ul in

  let is_pk_valid = load_point_vartime pk public_key in
  let is_rs_valid = load_signature r_q s_q signature_r signature_s in

  let res =
    if not (is_pk_valid && is_rs_valid) then false
    else begin
      ecdsa_verification_get_u12 u1 u2 r_q s_q m_q;
      ecdsa_verification_cmpr r_q pk u1 u2 end in
  pop_frame ();
  res
