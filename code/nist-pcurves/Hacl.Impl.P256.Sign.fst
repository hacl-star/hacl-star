module Hacl.Impl.P256.Sign

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.PointMul


module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module QI = Hacl.Impl.P256.Qinv
module BB = Hacl.Bignum.Base
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

inline_for_extraction noextract
val ecdsa_sign_r (r k:felem) : Stack unit
  (requires fun h ->
    live h r /\ live h k /\ disjoint r k /\
    as_nat h k < S.order)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\
   (let x, _ = S.to_aff_point (S.point_mul_g (as_nat h0 k)) in
    as_nat h1 r == x % S.order))

let ecdsa_sign_r r k =
  push_frame ();
  let p = create_point () in
  point_mul_g p k; // p = [k]G
  to_aff_point_x r p;
  qmod_short r r;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_s (s k r d_a m:felem) : Stack unit
  (requires fun h ->
    live h s /\ live h m /\ live h d_a /\ live h k /\ live h r /\
    disjoint s r /\ disjoint s k /\ disjoint r k /\
    disjoint s d_a /\ disjoint r d_a /\ disjoint m s /\

    0 < as_nat h k /\ as_nat h k < S.order /\
    as_nat h r < S.order /\ as_nat h m < S.order /\
    0 < as_nat h d_a /\ as_nat h d_a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc s |+| loc m) h0 h1 /\
   (let kinv = S.qinv (as_nat h0 k) in
    as_nat h1 s == S.qmul kinv (S.qadd (as_nat h0 m) (S.qmul (as_nat h0 r) (as_nat h0 d_a)))))

let ecdsa_sign_s s k r d_a m =
  push_frame ();
  let h0 = ST.get () in
  let kinv = create_felem () in
  QI.qinv kinv k;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 kinv == S.qinv (qmont_as_nat h0 k));
  SM.qmont_inv_lemma (as_nat h0 k);
  assert (qmont_as_nat h1 kinv == S.qinv (as_nat h0 k) * SM.qmont_R % S.order);

  qmul s r d_a;  // s = r * d_a
  let h2 = ST.get () in
  assert (as_nat h2 s == (as_nat h0 r * as_nat h0 d_a * SM.qmont_R_inv) % S.order);
  from_qmont m m;
  let h3 = ST.get () in
  assert (as_nat h3 m == as_nat h2 m * SM.qmont_R_inv % S.order);
  qadd s m s;    // s = z + s
  let h4 = ST.get () in
  assert (as_nat h4 s == (as_nat h3 m + as_nat h2 s) % S.order);
  qmul s kinv s; // s = kinv * s
  let h5 = ST.get () in
  assert (as_nat h5 s == (as_nat h1 kinv * as_nat h4 s * SM.qmont_R_inv) % S.order);
  SM.lemma_ecdsa_sign_s
    (as_nat h0 k) (as_nat h1 kinv) (as_nat h0 r) (as_nat h0 d_a) (as_nat h0 m);
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_load (d_a k_q:felem) (private_key nonce:lbytes 32ul) : Stack uint64
  (requires fun h ->
    live h private_key /\ live h nonce /\ live h d_a /\ live h k_q /\
    disjoint d_a k_q /\ disjoint d_a private_key /\ disjoint d_a nonce /\
    disjoint k_q private_key /\ disjoint k_q nonce)
  (ensures fun h0 m h1 -> modifies (loc d_a |+| loc k_q) h0 h1 /\
   (let d_a_nat = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    let k_nat = BSeq.nat_from_bytes_be (as_seq h0 nonce) in
    let is_sk_valid = 0 < d_a_nat && d_a_nat < S.order in
    let is_nonce_valid = 0 < k_nat && k_nat < S.order in
    (v m = ones_v U64 \/ v m = 0) /\
    (v m = ones_v U64) = (is_sk_valid && is_nonce_valid) /\
    as_nat h1 d_a == (if is_sk_valid then d_a_nat else 1) /\
    as_nat h1 k_q == (if is_nonce_valid then k_nat else 1)))

let ecdsa_sign_load d_a k_q private_key nonce =
  let is_sk_valid = load_qelem_conditional d_a private_key in
  let is_nonce_valid = load_qelem_conditional k_q nonce in
  let m = is_sk_valid &. is_nonce_valid in
  logand_lemma is_sk_valid is_nonce_valid;
  m


inline_for_extraction noextract
val check_signature: are_sk_nonce_valid:uint64 -> r_q:felem -> s_q:felem -> Stack bool
  (requires fun h ->
    live h r_q /\ live h s_q /\ disjoint r_q s_q /\
    (v are_sk_nonce_valid = ones_v U64 \/ v are_sk_nonce_valid = 0))
  (ensures fun h0 res h1 -> modifies0 h0 h1 /\
    res == ((v are_sk_nonce_valid = ones_v U64) && (0 < as_nat h0 r_q) && (0 < as_nat h0 s_q)))

let check_signature are_sk_nonce_valid r_q s_q =
  let h0 = ST.get () in
  let is_r_zero = bn_is_zero_mask4 r_q in
  let is_s_zero = bn_is_zero_mask4 s_q in
  [@inline_let] let m0 = lognot is_r_zero in
  [@inline_let] let m1 = lognot is_s_zero in
  [@inline_let] let m2 = m0 &. m1 in
  lognot_lemma is_r_zero;
  lognot_lemma is_s_zero;
  logand_lemma m0 m1;
  let m = are_sk_nonce_valid &. m2 in
  logand_lemma are_sk_nonce_valid m2;
  assert ((v m = ones_v U64) <==>
    ((v are_sk_nonce_valid = ones_v U64) && (0 < as_nat h0 r_q) && (0 < as_nat h0 s_q)));
  BB.unsafe_bool_of_limb m


val ecdsa_sign_msg_as_qelem:
    signature:lbuffer uint8 64ul
  -> m_q:felem
  -> private_key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h signature /\ live h m_q /\ live h private_key /\ live h nonce /\
    disjoint signature m_q /\ disjoint signature private_key /\ disjoint signature nonce /\
    disjoint m_q private_key /\ disjoint m_q nonce /\
    as_nat h m_q < S.order)
  (ensures fun h0 flag h1 -> modifies (loc signature |+| loc m_q) h0 h1 /\
    (let sgnt = S.ecdsa_sign_msg_as_qelem
      (as_nat h0 m_q) (as_seq h0 private_key) (as_seq h0 nonce) in
     (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 signature == Some?.v sgnt))))

[@CInline]
let ecdsa_sign_msg_as_qelem signature m_q private_key nonce =
  push_frame ();
  let rsdk_q = create 16ul (u64 0) in
  let r_q = sub rsdk_q 0ul 4ul in
  let s_q = sub rsdk_q 4ul 4ul in
  let d_a = sub rsdk_q 8ul 4ul in
  let k_q = sub rsdk_q 12ul 4ul in
  let are_sk_nonce_valid = ecdsa_sign_load d_a k_q private_key nonce in
  ecdsa_sign_r r_q k_q;
  ecdsa_sign_s s_q k_q r_q d_a m_q;
  bn2_to_bytes_be4 signature r_q s_q;
  let res = check_signature are_sk_nonce_valid r_q s_q in
  pop_frame ();
  res
