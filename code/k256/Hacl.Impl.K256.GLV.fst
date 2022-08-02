module Hacl.Impl.K256.GLV

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PM = Hacl.Impl.K256.PointMul

module S = Spec.K256
module SG = Hacl.Spec.K256.GLV
module SGL = Hacl.Spec.K256.GLV.Lemmas

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point

open Hacl.Impl.K256.GLV.Constants

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
val scalar_split_lambda_g1g2 (tmp1 tmp2 k1 k2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h k1 /\ live h k2 /\
    live h tmp1 /\ live h tmp2 /\
    disjoint k k1 /\ disjoint k k2 /\ disjoint k1 k2 /\
    disjoint tmp1 k1 /\ disjoint tmp1 k2 /\ disjoint tmp1 k /\
    disjoint tmp2 k1 /\ disjoint tmp2 k2 /\ disjoint tmp2 k /\
    disjoint tmp1 tmp2 /\ qas_nat h k < S.q)
  (ensures  fun h0 _ h1 ->
    modifies (loc k1 |+| loc k2 |+| loc tmp1 |+| loc tmp2) h0 h1 /\
   (let k1 = qas_nat h1 k1 in let k2 = qas_nat h1 k2 in
    k1 < S.q /\ k1 = SG.qmul_shift_384 (qas_nat h0 k) SG.g1 /\
    k2 < S.q /\ k2 = SG.qmul_shift_384 (qas_nat h0 k) SG.g2))

let scalar_split_lambda_g1g2 tmp1 tmp2 k1 k2 k =
  make_g1 tmp1; // tmp1 = g1
  make_g2 tmp2; // tmp2 = g2
  qmul_shift_384 k1 k tmp1; // k1 = c1 = qmul_shift_384 k g1
  qmul_shift_384 k2 k tmp2; // k2 = c2 = qmul_shift_384 k g2
  let h0 = ST.get () in
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp1);
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp2);
  assert (qas_nat h0 k1 < S.q /\ qas_nat h0 k2 < S.q)


val scalar_split_lambda (k1 k2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h k1 /\ live h k2 /\
    disjoint k k1 /\ disjoint k k2 /\ disjoint k1 k2 /\
    qas_nat h k < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc k1 |+| loc k2) h0 h1 /\
   (let k1_s, k2_s = SG.scalar_split_lambda (qas_nat h0 k) in
    let k1 = qas_nat h1 k1 in let k2 = qas_nat h1 k2 in
    k1 < S.q /\ k1 == k1_s /\ k2 < S.q /\ k2 == k2_s /\
    k1 < pow2 129 /\ k2 < pow2 129))

[@CInline]
let scalar_split_lambda k1 k2 k =
  let h0 = ST.get () in
  SGL.lemma_scalar_split_lambda_fits (qas_nat h0 k);
  push_frame ();
  let tmp1 = create_qelem () in
  let tmp2 = create_qelem () in
  scalar_split_lambda_g1g2 tmp1 tmp2 k1 k2 k;

  make_minus_b1 tmp1; // tmp1 = minus_b1
  make_minus_b2 tmp2; // tmp2 = minus_b2
  qmul k1 k1 tmp1; // k1 = c1 = c1 * minus_b1
  qmul k2 k2 tmp2; // k2 = c2 = c2 * minus_b2

  make_minus_lambda tmp1; // tmp1 = minus_lambda
  qadd k2 k1 k2; // k2 = r2 = c1 + c2
  qmul tmp2 k2 tmp1; // tmp2 = r2 * minus_lambda
  qadd k1 k tmp2; // k1 = r1 = k + r2 * minus_lambda
  pop_frame ()


// [lambda]P = (beta * px, py, pz)
inline_for_extraction noextract
val point_mul_lambda: res:point -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ eq_or_disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 p))

let point_mul_lambda res p =
  push_frame ();
  let rx, ry, rz = getx res, gety res, getz res in
  let px, py, pz = getx p, gety p, getz p in
  let beta = create_felem () in
  make_beta beta;
  fmul rx beta px;

  copy_felem ry py;
  copy_felem rz pz;
  pop_frame ()


// TODO: set it to a constant?
// [lambda]G
inline_for_extraction noextract
val point_mul_g_lambda: res:point -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_g_lambda ())

let point_mul_g_lambda res =
  push_frame ();
  let g = create_point () in
  PM.make_g g;
  point_mul_lambda res g;
  pop_frame ()


// TODO: share a table [0; P; 2P; ..; 15P] between P and ([lambda]P)
val point_mul_split_lambda: out:point -> scalar:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ live h q /\
    disjoint out q /\ disjoint out scalar /\ disjoint q scalar /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul (qas_nat h0 scalar) (point_eval h0 q))

[@CInline]
let point_mul_split_lambda out scalar q =
  let h0 = ST.get () in
  push_frame ();
  let q2 = create_point () in
  point_mul_lambda q2 q;

  let r1 = create_qelem () in
  let r2 = create_qelem () in
  scalar_split_lambda r1 r2 scalar;

  ME.lexp_double_fw_vartime 15ul 0ul PM.mk_k256_concrete_ops (null uint64)
    q 4ul 129ul r1 q2 r2 out 4ul;

  assume (
    SGL.point_mul_split_lambda (qas_nat h0 scalar) (point_eval h0 q) ==
    S.point_mul (qas_nat h0 scalar) (point_eval h0 q));
  pop_frame ()


// TODO: precompute a table [0; G; 2G; ..; 15G]?
val point_mul_g_split_lambda: out:point -> scalar:qelem -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ disjoint out scalar /\
    qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul_g (qas_nat h0 scalar))

[@CInline]
let point_mul_g_split_lambda out scalar =
  push_frame ();
  let g = create 15ul (u64 0) in
  PM.make_g g;
  point_mul_split_lambda out scalar g;
  pop_frame ()
