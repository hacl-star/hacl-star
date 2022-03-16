module Hacl.Impl.K256.Verify

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence

module S = Spec.K256
module KL = Spec.K256.Lemmas

open Hacl.K256.Field
open Hacl.Impl.K256.Point
open Hacl.Impl.K256.PointMul

module QA = Hacl.K256.Scalar
module QI = Hacl.Impl.K256.Qinv
module BI = Hacl.Spec.K256.Field52
module BL = Hacl.Spec.K256.Field52.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len


val load_public_key (pk:lbytes 64ul) (fpk_x fpk_y:felem) : Stack bool
  (requires fun h ->
    live h pk /\ live h fpk_x /\ live h fpk_y /\
    disjoint fpk_x fpk_y /\ disjoint fpk_x pk /\ disjoint fpk_y pk)
  (ensures  fun h0 b h1 -> modifies (loc fpk_x |+| loc fpk_y) h0 h1 /\
    (b ==> inv_fully_reduced h1 fpk_x /\ inv_fully_reduced h1 fpk_y) /\
    (as_nat h1 fpk_x, as_nat h1 fpk_y, b) == S.load_public_key (as_seq h0 pk))

[@CInline]
let load_public_key pk fpk_x fpk_y =
  let pk_x = sub pk 0ul 32ul in
  let pk_y = sub pk 32ul 32ul in
  let is_x_valid = load_felem_vartime fpk_x pk_x in
  let is_y_valid = load_felem_vartime fpk_y pk_y in

  let is_xy_on_curve =
    if is_x_valid && is_y_valid then
      is_on_curve_vartime fpk_x fpk_y
    else false in
  is_xy_on_curve


inline_for_extraction noextract
val ecdsa_verify_qelem (res p:point) (z r s:QA.qelem) : Stack unit
  (requires fun h ->
    live h res /\ live h p /\ live h z /\ live h r /\ live h s /\
    disjoint res p /\ point_inv h p /\
    QA.qas_nat h z < S.q /\ QA.qas_nat h r < S.q /\ QA.qas_nat h s < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\ point_inv h1 res /\
   (let sinv = S.qinv (QA.qas_nat h0 s) in
    let u1 = S.qmul (QA.qas_nat h0 z) sinv in
    let u2 = S.qmul (QA.qas_nat h0 r) sinv in
    point_eval h1 res == S.point_mul_double_g u1 u2 (point_eval h0 p)))

let ecdsa_verify_qelem res p z r s =
  push_frame ();
  let sinv = QA.create_qelem () in
  let u1 = QA.create_qelem () in
  let u2 = QA.create_qelem () in

  QI.qinv sinv s;
  QA.qmul u1 z sinv;
  QA.qmul u2 r sinv;
  point_mul_g_double_vartime res u1 u2 p;
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
val ecdsa_verify_qelem_aff (pk_x pk_y:felem) (z r s:QA.qelem) : Stack bool
  (requires fun h ->
    live h pk_x /\ live h pk_y /\ live h z /\ live h r /\ live h s /\
    QA.qas_nat h z < S.q /\ QA.qas_nat h s < S.q /\
    0 < QA.qas_nat h r /\ QA.qas_nat h r < S.q /\
    inv_fully_reduced h pk_x /\ inv_fully_reduced h pk_y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
   (let sinv = S.qinv (QA.qas_nat h0 s) in
    let u1 = S.qmul (QA.qas_nat h0 z) sinv in
    let u2 = S.qmul (QA.qas_nat h0 r) sinv in
    let p = (feval h0 pk_x, feval h0 pk_y, S.one) in
    let _X, _Y, _Z = S.point_mul_double_g u1 u2 p in
    b <==> (if S.is_proj_point_at_inf (_X, _Y, _Z) then false
      else S.fmul _X (S.finv _Z) % S.q = QA.qas_nat h0 r)))

let ecdsa_verify_qelem_aff pk_x pk_y z r s =
  push_frame ();
  let p = create_point () in
  let res = create_point () in

  to_proj_point p pk_x pk_y;
  ecdsa_verify_qelem res p z r s;

  let b =
    if is_proj_point_at_inf_vartime res then false
    else ecdsa_verify_avoid_finv res r in
  pop_frame ();
  b


inline_for_extraction noextract
val ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))

#push-options "--z3rlimit 150"
let ecdsa_verify_hashed_msg msgHash public_key signature =
  push_frame ();
  let pk_x = create_felem () in
  let pk_y = create_felem () in

  let r_q = QA.create_qelem () in
  let s_q = QA.create_qelem () in
  let z = QA.create_qelem () in

  let is_xy_on_curve = load_public_key public_key pk_x pk_y in
  let is_r_valid = QA.load_qelem_vartime r_q (sub signature 0ul 32ul) in
  let is_s_valid = QA.load_qelem_vartime s_q (sub signature 32ul 32ul) in
  QA.load_qelem_modq z msgHash;

  let h0 = ST.get () in
  let res =
    if not (is_xy_on_curve && is_r_valid && is_s_valid) then false
    else begin
      Math.Lemmas.small_mod (as_nat h0 pk_x) S.prime;
      Math.Lemmas.small_mod (as_nat h0 pk_y) S.prime;
      ecdsa_verify_qelem_aff pk_x pk_y z r_q s_q end in
  pop_frame ();
  res
#pop-options
