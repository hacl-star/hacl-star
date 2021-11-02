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
let lbytes32 = lbuffer uint8 32ul


inline_for_extraction noextract
val ecdsa_sign_r: r:qelem -> k:lbytes32 -> Stack unit
  (requires fun h -> live h r /\ live h k /\ disjoint r k)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\
   (let _X, _Y, _Z = S.point_mul_g (as_seq h0 k) in
    let x = S.fmul _X (S.finv _Z) in
    let r_s = x % S.q in
    qas_nat h1 r == r_s))

let ecdsa_sign_r r k =
  push_frame ();
  let p = create (3ul *! nlimb) (u64 0) in
  let x, y, z = getx p, gety p, getz p in
  let tmp = create_felem () in

  point_mul_g p k; // p = [k]G
  finv tmp z; // tmp = zinv
  fmul tmp x tmp; // tmp = aff_x = x *% zinv
  qelem_from_felem r tmp; // r = aff_x % S.q
  pop_frame ()


inline_for_extraction noextract
val ecdsa_sign_s (s:qelem) (m private_key k:lbytes32) (r:qelem) : Stack unit
  (requires fun h ->
    live h s /\ live h m /\ live h private_key /\
    live h k /\ live h r /\ disjoint s r /\

   (let sk_nat = BSeq.nat_from_bytes_be (as_seq h private_key) in
    let k_nat = BSeq.nat_from_bytes_be (as_seq h k) in
    0 < sk_nat /\ sk_nat < S.q /\
    0 < k_nat /\ k_nat < S.q /\
    qas_nat h r < S.q))
  (ensures fun h0 _ h1 -> modifies (loc s) h0 h1 /\
   (let z = BSeq.nat_from_bytes_be (as_seq h0 m) % S.q in
    let d_a = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    let kinv = S.qinv (BSeq.nat_from_bytes_be (as_seq h0 k)) in
    let s_s = S.qmul kinv (S.qadd z (S.qmul (qas_nat h0 r) d_a)) in
    qas_nat h1 s == s_s))

let ecdsa_sign_s s m private_key k r =
  push_frame ();
  let z = create_qelem () in
  let d_a = create_qelem () in
  let kinv = create_qelem () in

  load_qelem_modq z m; // z = m % S.q
  load_qelem d_a private_key; // d_a = private_key
  load_qelem kinv k;
  qinv kinv kinv;

  qmul s r d_a; // s = r * d_a
  qadd s z s; // s = z + s
  qmul s kinv s; // s = kinv * s
  pop_frame ()


[@CInline]
let ecdsa_sign_hashed_msg r s m private_key k =
  push_frame ();
  let r_q = create_qelem () in
  let s_q = create_qelem () in

  ecdsa_sign_r r_q k;
  ecdsa_sign_s s_q m private_key k r_q;

  store_qelem r r_q;
  store_qelem s s_q;

  let is_r_zero = is_qelem_zero_vartime r_q in
  let is_s_zero = is_qelem_zero_vartime s_q in
  let b =  if is_r_zero || is_s_zero then false else true in
  pop_frame ();
  b


[@CInline]
let ecdsa_verify_hashed_msg m public_key r s =
  admit()


[@CInline]
let ecdsa_sign_sha256 r s msg_len msg private_key k =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_sign_hashed_msg r s mHash private_key k in
  pop_frame ();
  b


[@CInline]
let ecdsa_verify_sha256 msg_len msg public_key r s =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_verify_hashed_msg mHash public_key r s in
  pop_frame ();
  b
