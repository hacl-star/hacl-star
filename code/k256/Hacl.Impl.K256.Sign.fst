module Hacl.Impl.K256.Sign

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module FI = Hacl.Impl.K256.Finv
module QI = Hacl.Impl.K256.Qinv

module S = Spec.K256

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point
open Hacl.Impl.K256.PointMul
open Hacl.Impl.K256.GLV

module BL = Hacl.Spec.K256.Field52.Lemmas
module BB = Hacl.Bignum.Base

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

inline_for_extraction noextract
val ecdsa_sign_r (r k:qelem) : Stack unit
  (requires fun h ->
    live h r /\ live h k /\ disjoint r k /\
    qas_nat h k < S.q)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\
   (let _X, _Y, _Z = S.point_mul_g (qas_nat h0 k) in
    let x = S.fmul _X (S.finv _Z) in
    let r_s = x % S.q in
    qas_nat h1 r == r_s))

let ecdsa_sign_r r k =
  push_frame ();
  let tmp = create_felem () in
  let x_bytes = create 32ul (u8 0) in

  let p = create_point () in
  // point_mul_g p k; // p = [k]G
  point_mul_g_split_lambda p k; // p = [k]G
  let x, y, z = getx p, gety p, getz p in

  FI.finv tmp z; // tmp = zinv
  fmul tmp x tmp; // tmp = aff_x = x *% zinv
  let h1 = ST.get () in
  //assert (inv_lazy_reduced2 h1 tmp);
  fnormalize tmp tmp;
  let h2 = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h1 tmp);

  store_felem x_bytes tmp;
  load_qelem_modq r x_bytes; // r = aff_x % S.q
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_s (s k r d_a:qelem) (m:lbytes 32ul) : Stack unit
  (requires fun h ->
    live h s /\ live h m /\ live h d_a /\ live h k /\ live h r /\
    disjoint s r /\ disjoint s k /\ disjoint r k /\
    disjoint s d_a /\ disjoint r d_a /\

    0 < qas_nat h k /\ qas_nat h k < S.q /\
    qas_nat h r < S.q /\
    0 < qas_nat h d_a /\ qas_nat h d_a < S.q)
  (ensures fun h0 _ h1 -> modifies (loc s) h0 h1 /\
   (let z = BSeq.nat_from_bytes_be (as_seq h0 m) % S.q in
    let kinv = S.qinv (qas_nat h0 k) in
    let s_s = S.qmul kinv (S.qadd z (S.qmul (qas_nat h0 r) (qas_nat h0 d_a))) in
    qas_nat h1 s == s_s))

let ecdsa_sign_s s k r d_a m =
  push_frame ();
  let z = create_qelem () in
  let kinv = create_qelem () in

  load_qelem_modq z m; // z = m % S.q
  QI.qinv kinv k;

  qmul s r d_a; // s = r * d_a
  qadd s z s; // s = z + s
  qmul s kinv s; // s = kinv * s
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_load (d_a k_q:qelem) (private_key nonce:lbytes 32ul) : Stack uint64
  (requires fun h ->
    live h private_key /\ live h nonce /\ live h d_a /\ live h k_q /\
    disjoint d_a k_q /\ disjoint d_a private_key /\ disjoint d_a nonce /\
    disjoint k_q private_key /\ disjoint k_q nonce)
  (ensures fun h0 m h1 -> modifies (loc d_a |+| loc k_q) h0 h1 /\
   (let sk_nat = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    let k_nat = BSeq.nat_from_bytes_be (as_seq h0 nonce) in
    qas_nat h1 d_a = sk_nat /\ qas_nat h1 k_q = k_nat /\
    (v m = ones_v U64 \/ v m = 0) /\
    (v m = ones_v U64) = (0 < sk_nat && sk_nat < S.q && 0 < k_nat && k_nat < S.q)))

let ecdsa_sign_load d_a k_q private_key nonce =
  let is_sk_valid = load_qelem_check d_a private_key in
  let is_nonce_valid = load_qelem_check k_q nonce in
  let m = is_sk_valid &. is_nonce_valid in
  logand_lemma is_sk_valid is_nonce_valid;
  m


inline_for_extraction noextract
val ecdsa_sign_store (signature:lbytes 64ul) (r_q s_q:qelem) : Stack unit
  (requires fun h ->
    live h signature /\ live h r_q /\ live h s_q /\
    disjoint signature r_q /\ disjoint signature s_q /\
    qas_nat h r_q < S.q /\ qas_nat h s_q < S.q)
  (ensures fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
   (let r = BSeq.nat_to_bytes_be 32 (qas_nat h0 r_q) in
    let s = BSeq.nat_to_bytes_be 32 (qas_nat h0 s_q) in
    as_seq h1 signature == LSeq.concat #_ #32 #32 r s))

let ecdsa_sign_store signature r_q s_q =
  let h0 = ST.get () in
  update_sub_f h0 signature 0ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (qas_nat h0 r_q))
    (fun _ -> store_qelem (sub signature 0ul 32ul) r_q);

  let h1 = ST.get () in
  update_sub_f h1 signature 32ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (qas_nat h1 s_q))
    (fun _ -> store_qelem (sub signature 32ul 32ul) s_q);

  let h2 = ST.get () in
  let r = Ghost.hide (BSeq.nat_to_bytes_be 32 (qas_nat h0 r_q)) in
  let s = Ghost.hide (BSeq.nat_to_bytes_be 32 (qas_nat h0 s_q)) in
  LSeq.eq_intro (as_seq h2 signature) (LSeq.concat #_ #32 #32 r s)


inline_for_extraction noextract
val ecdsa_sign_hashed_msg (signature:lbytes 64ul) (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))

let ecdsa_sign_hashed_msg signature msgHash private_key nonce =
  push_frame ();
  let r_q = create_qelem () in
  let s_q = create_qelem () in
  let d_a = create_qelem () in
  let k_q = create_qelem () in

  let are_sk_nonce_valid = ecdsa_sign_load d_a k_q private_key nonce in

  let b =
    if BB.unsafe_bool_of_limb0 are_sk_nonce_valid then false
    else begin
      ecdsa_sign_r r_q k_q;
      ecdsa_sign_s s_q k_q r_q d_a msgHash;
      ecdsa_sign_store signature r_q s_q;

      let is_r_zero = is_qelem_zero r_q in
      let is_s_zero = is_qelem_zero s_q in
      if BB.unsafe_bool_of_limb is_r_zero || BB.unsafe_bool_of_limb is_s_zero
      then false else true end in
  pop_frame ();
  b
