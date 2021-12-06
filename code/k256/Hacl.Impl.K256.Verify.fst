module Hacl.Impl.K256.Verify

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module BD = Hacl.Bignum.Definitions

module QI = Hacl.Impl.K256.Qinv

module S = Spec.K256
module KL = Spec.K256.Lemmas

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point
open Hacl.Impl.K256.PointMul


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes32 = lbuffer uint8 32ul

inline_for_extraction noextract
val is_public_key_valid (pk_x pk_y:lbytes32) (fpk_x fpk_y:felem) : Stack bool
  (requires fun h ->
    live h pk_x /\ live h pk_y /\ live h fpk_x /\ live h fpk_y /\
    disjoint fpk_x fpk_y /\ disjoint fpk_x pk_x /\ disjoint fpk_x pk_y /\
    disjoint fpk_y pk_y /\ disjoint fpk_y pk_x)
  (ensures  fun h0 b h1 -> modifies (loc fpk_x |+| loc fpk_y) h0 h1 /\
    (as_nat h1 fpk_x, as_nat h1 fpk_y, b) ==
      S.is_public_key_valid (as_seq h0 pk_x) (as_seq h0 pk_y))

let is_public_key_valid pk_x pk_y fpk_x fpk_y =
  let is_x_valid = load_felem_vartime fpk_x pk_x in
  let is_y_valid = load_felem_vartime fpk_y pk_y in

  let is_xy_on_curve =
    if is_x_valid && is_y_valid then
      is_on_curve_vartime fpk_x fpk_y
    else false in
  is_xy_on_curve


inline_for_extraction noextract
val ecdsa_verify_qelem (res p:point) (z r s:qelem) : Stack unit
  (requires fun h ->
    live h res /\ live h p /\ live h z /\ live h r /\ live h s /\
    disjoint res p /\ point_inv h p /\
    qas_nat h z < S.q /\ qas_nat h r < S.q /\ qas_nat h s < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\ point_inv h1 res /\
   (let sinv = S.qinv (qas_nat h0 s) in
    let u1 = S.qmul (qas_nat h0 z) sinv in
    let u2 = S.qmul (qas_nat h0 r) sinv in
    S.to_aff_point (point_as_nat3_proj h1 res) ==
    S.to_aff_point (S.point_mul_double_g u1 u2 (point_as_nat3_proj h0 p))))

let ecdsa_verify_qelem res p z r s =
  push_frame ();
  let sinv = create_qelem () in
  let u1 = create_qelem () in
  let u2 = create_qelem () in

  QI.qinv sinv s;
  qmul u1 z sinv;
  qmul u2 r sinv;
  point_mul_g_double_vartime res u1 u2 p;
  pop_frame ()


inline_for_extraction noextract
val fmul_eq_vartime (r z x: felem) : Stack bool
  (requires fun h ->
    live h r /\ live h z /\ live h x /\ eq_or_disjoint r z /\
    fe_lt_prime h r /\ fe_lt_prime h z /\ fe_lt_prime h x)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == (S.fmul (as_nat h0 r) (as_nat h0 z) = as_nat h0 x))

let fmul_eq_vartime r z x =
  push_frame ();
  let tmp = create_felem () in
  fmul tmp r z;
  let b = is_felem_eq_vartime tmp x in
  pop_frame ();
  b


inline_for_extraction noextract
val ecdsa_verify_avoid_finv: p:point -> r:qelem -> Stack bool
  (requires fun h ->
    live h p /\ live h r /\ disjoint p r /\
    point_inv h p /\ qe_lt_q h r /\ 0 < qas_nat h r /\
    not (S.is_proj_point_at_inf (point_as_nat3_proj h p)))
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (let (_X, _Y, _Z) = point_as_nat3_proj h0 p in
     b <==> (S.fmul _X (S.finv _Z) % S.q = qas_nat h0 r)))

let ecdsa_verify_avoid_finv p r =
  push_frame ();
  let h0 = ST.get () in
  let x, y, z = getx p, gety p, getz p in
  let is_rz_x = fmul_eq_vartime r z x in

  let tmp = create_felem () in
  make_u64_4 tmp (make_order_k256 ());
  let is_tmp_lt_p = add_vartime tmp r tmp in
  let is_tmpz_x = if is_tmp_lt_p then fmul_eq_vartime tmp z x else false in

  let res = is_rz_x || is_tmpz_x in
  KL.ecdsa_verify_avoid_finv (point_as_nat3_proj h0 p) (qas_nat h0 r);
  pop_frame ();
  res


inline_for_extraction noextract
val ecdsa_verify_qelem_aff (pk_x pk_y:felem) (z r s:qelem) : Stack bool
  (requires fun h ->
    live h pk_x /\ live h pk_y /\ live h z /\ live h r /\ live h s /\
    qas_nat h z < S.q /\ qas_nat h s < S.q /\
    0 < qas_nat h r /\ qas_nat h r < S.q /\
    fe_lt_prime h pk_x /\ fe_lt_prime h pk_y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
   (let sinv = S.qinv (qas_nat h0 s) in
    let u1 = S.qmul (qas_nat h0 z) sinv in
    let u2 = S.qmul (qas_nat h0 r) sinv in
    let p = (as_nat h0 pk_x, as_nat h0 pk_y, S.one) in
    let _X, _Y, _Z = S.point_mul_double_g u1 u2 p in
    b <==> (if S.is_proj_point_at_inf (_X, _Y, _Z) then false
      else S.fmul _X (S.finv _Z) % S.q = qas_nat h0 r)))

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
val ecdsa_verify_hashed_msg (m public_key_x public_key_y r s:lbytes32) : Stack bool
  (requires fun h ->
    live h m /\ live h public_key_x /\ live h public_key_y /\
    live h r /\ live h s /\ disjoint r s)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 m)
      (as_seq h0 public_key_x) (as_seq h0 public_key_y) (as_seq h0 r) (as_seq h0 s))

#push-options "--z3rlimit 150"
let ecdsa_verify_hashed_msg m public_key_x public_key_y r s =
  push_frame ();
  let pk_x = create_felem () in
  let pk_y = create_felem () in

  let r_q = create_qelem () in
  let s_q = create_qelem () in
  let z = create_qelem () in

  let is_xy_on_curve = is_public_key_valid public_key_x public_key_y pk_x pk_y in
  let is_r_valid = load_qelem_vartime r_q r in
  let is_s_valid = load_qelem_vartime s_q s in
  load_qelem_modq z m;

  let res =
    if not (is_xy_on_curve && is_r_valid && is_s_valid) then false
    else ecdsa_verify_qelem_aff pk_x pk_y z r_q s_q in
  pop_frame ();
  res
#pop-options
