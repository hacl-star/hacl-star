module Hacl.Impl.K256.Verify

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module S = Spec.K256
module KL = Spec.K256.Lemmas

open Hacl.K256.Field
open Hacl.Impl.K256.Point
open Hacl.Impl.K256.PointMul
open Hacl.Impl.K256.GLV

module QA = Hacl.K256.Scalar
module QI = Hacl.Impl.K256.Qinv
module BL = Hacl.Spec.K256.Field52.Lemmas
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

inline_for_extraction noextract
val ecdsa_verify_get_u12 (u1 u2 r s z: QA.qelem) : Stack unit
  (requires fun h ->
    live h r /\ live h s /\ live h z /\ live h u1 /\ live h u2 /\
    disjoint u1 u2 /\ disjoint u1 z /\ disjoint u1 r /\ disjoint u1 s /\
    disjoint u2 z /\ disjoint u2 r /\ disjoint u2 s /\
    QA.qas_nat h s < S.q /\ QA.qas_nat h z < S.q /\ QA.qas_nat h r < S.q)
  (ensures fun h0 _ h1 -> modifies (loc u1 |+| loc u2) h0 h1 /\
    (let sinv = S.qinv (QA.qas_nat h0 s) in
    QA.qas_nat h1 u1 == QA.qas_nat h0 z * sinv % S.q /\
    QA.qas_nat h1 u2 == QA.qas_nat h0 r * sinv % S.q))

let ecdsa_verify_get_u12 u1 u2 r s z =
  push_frame ();
  let sinv = QA.create_qelem () in
  QI.qinv sinv s;
  QA.qmul u1 z sinv;
  QA.qmul u2 r sinv;
  pop_frame ()


val fmul_eq_vartime (r z x: felem) : Stack bool
  (requires fun h ->
    live h r /\ live h z /\ live h x /\ eq_or_disjoint r z /\
    felem_fits5 (as_felem5 h r) (2,2,2,2,2) /\ as_nat h r < S.prime /\
    inv_lazy_reduced2 h z /\ inv_fully_reduced h x)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == (S.fmul (as_nat h0 r) (feval h0 z) = as_nat h0 x))

[@CInline]
let fmul_eq_vartime r z x =
  push_frame ();
  let tmp = create_felem () in
  fmul tmp r z;
  let h1 = ST.get () in
  fnormalize tmp tmp;
  let h2 = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h1 tmp);
  assert (inv_fully_reduced h2 tmp);
  let b = is_felem_eq_vartime tmp x in
  pop_frame ();
  b


inline_for_extraction noextract
val ecdsa_verify_avoid_finv: p:point -> r:QA.qelem -> Stack bool
  (requires fun h ->
    live h p /\ live h r /\ disjoint p r /\
    point_inv h p /\ QA.qe_lt_q h r /\ 0 < QA.qas_nat h r /\
    not (S.is_proj_point_at_inf (point_eval h p)))
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (let (_X, _Y, _Z) = point_eval h0 p in
     b <==> (S.fmul _X (S.finv _Z) % S.q = QA.qas_nat h0 r)))

let ecdsa_verify_avoid_finv p r =
  let h0 = ST.get () in
  let x, y, z = getx p, gety p, getz p in

  push_frame ();
  let r_bytes = create 32ul (u8 0) in
  let r_fe = create_felem () in
  let tmp_q = create_felem () in
  let tmp_x = create_felem () in

  QA.store_qelem r_bytes r;
  load_felem r_fe r_bytes;
  let h1 = ST.get () in
  //assert (inv_fully_reduced h1 r_fe);
  //assert (as_nat h1 r_fe == qas_nat h1 r);

  let h2 = ST.get () in
  fnormalize tmp_x x;
  let h3 = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h2 x);
  //assert (inv_fully_reduced h3 tmp_x);
  //assert (inv_lazy_reduced2 h3 z);

  let is_rz_x = fmul_eq_vartime r_fe z tmp_x in
  //assert (is_rz_x == (S.fmul (as_nat h3 r_fe) (feval h3 z) = as_nat h3 tmp_x));

  let res : bool =
    if not is_rz_x then begin
     let is_r_lt_p_m_q = is_felem_lt_prime_minus_order_vartime r_fe in
     if is_r_lt_p_m_q then begin
       assert (as_nat h1 r_fe < S.prime - S.q);
       make_u52_5 tmp_q (make_order_k256 ());
       let h4 = ST.get () in
       BL.add5_lemma (1,1,1,1,1) (1,1,1,1,1) (as_felem5 h4 r_fe) (as_felem5 h4 tmp_q);
       fadd tmp_q r_fe tmp_q;
       fmul_eq_vartime tmp_q z tmp_x end
       //assert (is_rqz_x == (S.fmul (feval h5 tmp) (feval h5 z) = as_nat h5 tmp_x));
     else false end
    else true in

  pop_frame ();
  KL.ecdsa_verify_avoid_finv (point_eval h0 p) (QA.qas_nat h0 r);
  assert (res <==> (S.fmul (feval h0 x) (S.finv (feval h0 z)) % S.q = QA.qas_nat h0 r));
  let h5 = ST.get () in
  assert (modifies0 h0 h5);
  res


inline_for_extraction noextract
val ecdsa_verify_cmpr: r:QA.qelem -> pk:point -> u1:QA.qelem -> u2:QA.qelem -> Stack bool
  (requires fun h ->
    live h r /\ live h pk /\ live h u1 /\ live h u2 /\
    disjoint r u1 /\ disjoint r u2 /\ disjoint r pk /\
    disjoint pk u1 /\ disjoint pk u2 /\
    point_inv h pk /\ QA.qas_nat h u1 < S.q /\ QA.qas_nat h u2 < S.q /\
    0 < QA.qas_nat h r /\ QA.qas_nat h r < S.q)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    (let _X, _Y, _Z = S.point_mul_double_g (QA.qas_nat h0 u1) (QA.qas_nat h0 u2)
      (point_eval h0 pk) in
    b <==> (if S.is_proj_point_at_inf (_X, _Y, _Z) then false
      else S.fmul _X (S.finv _Z) % S.q = QA.qas_nat h0 r)))

let ecdsa_verify_cmpr r pk u1 u2 =
  push_frame ();
  let res = create_point () in
  let h0 = ST.get () in
  point_mul_g_double_split_lambda_vartime res u1 u2 pk;
  let h1 = ST.get () in
  assert (S.to_aff_point (point_eval h1 res) ==
    S.to_aff_point (S.point_mul_double_g (QA.qas_nat h0 u1) (QA.qas_nat h0 u2)
      (point_eval h0 pk)));

  KL.lemma_aff_is_point_at_inf (point_eval h1 res);
  KL.lemma_aff_is_point_at_inf (S.point_mul_double_g (QA.qas_nat h0 u1) (QA.qas_nat h0 u2)
      (point_eval h0 pk));

  let b =
    if is_proj_point_at_inf_vartime res then false
    else ecdsa_verify_avoid_finv res r in
  pop_frame ();
  b


inline_for_extraction noextract
val load_signature (r_q s_q:QA.qelem) (signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h signature /\ live h r_q /\ live h s_q /\
    disjoint r_q s_q /\ disjoint r_q signature /\ disjoint s_q signature)
  (ensures fun h0 res h1 -> modifies (loc r_q |+| loc s_q) h0 h1 /\
   (let sign_r = gsub signature 0ul 32ul in
    let sign_s = gsub signature 32ul 32ul in
    let r_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_r) in
    let s_q_nat = BSeq.nat_from_bytes_be (as_seq h0 sign_s) in
    QA.qas_nat h1 r_q = r_q_nat /\ QA.qas_nat h1 s_q = s_q_nat /\
    res == (0 < r_q_nat && r_q_nat < S.q && 0 < s_q_nat && s_q_nat < S.q)))

let load_signature r_q s_q signature =
  let is_r_valid = QA.load_qelem_vartime r_q (sub signature 0ul 32ul) in
  let is_s_valid = QA.load_qelem_vartime s_q (sub signature 32ul 32ul) in
  is_r_valid && is_s_valid


inline_for_extraction noextract
val ecdsa_verify_hashed_msg (msgHash:lbytes 32ul)
  (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))

let ecdsa_verify_hashed_msg msgHash public_key signature =
  push_frame ();
  let tmp = create 35ul (u64 0) in
  let pk  = sub tmp 0ul 15ul in
  let r_q = sub tmp 15ul 4ul in
  let s_q = sub tmp 19ul 4ul in
  let u1  = sub tmp 23ul 4ul in
  let u2  = sub tmp 27ul 4ul in
  let m_q = sub tmp 31ul 4ul in

  let is_pk_valid = load_point_vartime pk public_key in
  let is_rs_valid = load_signature r_q s_q signature in
  QA.load_qelem_modq m_q msgHash;

  let res =
    if not (is_pk_valid && is_rs_valid) then false
    else begin
      ecdsa_verify_get_u12 u1 u2 r_q s_q m_q;
      ecdsa_verify_cmpr r_q pk u1 u2 end in
  pop_frame ();
  res
