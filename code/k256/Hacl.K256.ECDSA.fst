module Hacl.K256.ECDSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module BD = Hacl.Bignum.Definitions

module S = Spec.K256

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point
open Hacl.Impl.K256.PointMul


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

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
  let p = create_point () in
  point_mul_g p k; // p = [k]G
  let x, y, z = getx p, gety p, getz p in

  finv tmp z; // tmp = zinv
  fmul tmp x tmp; // tmp = aff_x = x *% zinv
  qelem_from_felem r tmp; // r = aff_x % S.q
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_s (s k r:qelem) (m private_key:lbytes32) : Stack unit
  (requires fun h ->
    live h s /\ live h m /\ live h private_key /\
    live h k /\ live h r /\
    disjoint s r /\ disjoint s k /\ disjoint r k /\

    0 < qas_nat h k /\ qas_nat h k < S.q /\
    qas_nat h r < S.q /\
   (let d_a = BSeq.nat_from_bytes_be (as_seq h private_key) in
    0 < d_a /\ d_a < S.q))
  (ensures fun h0 _ h1 -> modifies (loc s) h0 h1 /\
   (let z = BSeq.nat_from_bytes_be (as_seq h0 m) % S.q in
    let d_a = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    let kinv = S.qinv (qas_nat h0 k) in
    let s_s = S.qmul kinv (S.qadd z (S.qmul (qas_nat h0 r) d_a)) in
    qas_nat h1 s == s_s))

let ecdsa_sign_s s k r m private_key =
  push_frame ();
  let z = create_qelem () in
  let d_a = create_qelem () in
  let kinv = create_qelem () in

  load_qelem_modq z m; // z = m % S.q
  load_qelem d_a private_key; // d_a = private_key
  qinv kinv k;

  qmul s r d_a; // s = r * d_a
  qadd s z s; // s = z + s
  qmul s kinv s; // s = kinv * s
  pop_frame ()


[@CInline]
let ecdsa_sign_hashed_msg r s m private_key k =
  push_frame ();
  let r_q = create_qelem () in
  let s_q = create_qelem () in
  let k_q = create_qelem () in

  load_qelem k_q k;
  ecdsa_sign_r r_q k_q;
  ecdsa_sign_s s_q k_q r_q m private_key;

  store_qelem r r_q;
  store_qelem s s_q;

  let is_r_zero = is_qelem_zero_vartime r_q in
  let is_s_zero = is_qelem_zero_vartime s_q in
  let b =  if is_r_zero || is_s_zero then false else true in
  pop_frame ();
  b


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

  qinv sinv s;
  qmul u1 z sinv;
  qmul u2 r sinv;
  point_mul_g_double_vartime res u1 u2 p;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verify_qelem_aff (pk_x pk_y:felem) (z r s:qelem) : Stack bool
  (requires fun h ->
    live h pk_x /\ live h pk_y /\ live h z /\ live h r /\ live h s /\
    qas_nat h z < S.q /\ qas_nat h r < S.q /\ qas_nat h s < S.q /\
    fe_lt_prime h pk_x /\ fe_lt_prime h pk_y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (let sinv = S.qinv (qas_nat h0 s) in
     let u1 = S.qmul (qas_nat h0 z) sinv in
     let u2 = S.qmul (qas_nat h0 r) sinv in
     let p = (as_nat h0 pk_x, as_nat h0 pk_y, S.one) in
     let _X, _Y, _Z = S.point_mul_double_g u1 u2 p in
     b = (S.fmul _X (S.finv _Z) % S.q = (qas_nat h0 r))))

let ecdsa_verify_qelem_aff pk_x pk_y z r s =
  push_frame ();
  let p = create_point () in
  let res = create_point () in
  let zinv = create_felem () in
  let xq = create_qelem () in

  to_proj_point p pk_x pk_y;
  ecdsa_verify_qelem res p z r s;
  let _X, _Y, _Z = getx res, gety res, getz res in

  finv zinv _Z;
  fmul zinv _X zinv;
  qelem_from_felem xq zinv;
  let b = is_qelem_eq_vartime xq r in
  pop_frame ();
  b

#push-options "--z3rlimit 150"
[@CInline]
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


[@CInline]
let ecdsa_sign_sha256 r s msg_len msg private_key k =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_sign_hashed_msg r s mHash private_key k in
  pop_frame ();
  b


[@CInline]
let ecdsa_verify_sha256 msg_len msg public_key_x public_key_y r s =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_verify_hashed_msg mHash public_key_x public_key_y r s in
  pop_frame ();
  b
