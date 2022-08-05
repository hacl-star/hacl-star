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
module PT = Hacl.Impl.PrecompTable

module S = Spec.K256
module SG = Hacl.Spec.K256.GLV
module SGL = Hacl.Spec.K256.GLV.Lemmas
module SE = Spec.Exponentiation

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


// k = (k1 + lambda * k2) % S.q
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

// [lambda]P = (beta * px, py, pz)
inline_for_extraction noextract
val point_mul_lambda_inplace: res:point -> Stack unit
  (requires fun h ->
    live h res /\ point_inv h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 res))

let point_mul_lambda_inplace res =
  push_frame ();
  let rx, ry, rz = getx res, gety res, getz res in
  let beta = create_felem () in
  make_beta beta;
  fmul rx beta rx;
  pop_frame ()


// // TODO: set it to a constant?
// // [lambda]G
// inline_for_extraction noextract
// val point_mul_g_lambda: res:point -> Stack unit
//   (requires fun h -> live h res)
//   (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
//     point_inv h1 res /\
//     point_eval h1 res == SG.point_mul_g_lambda ())

// let point_mul_g_lambda res =
//   push_frame ();
//   let g = create_point () in
//   PM.make_g g;
//   point_mul_lambda res g;
//   pop_frame ()

inline_for_extraction noextract
let table1_inv_precomp (q:LSeq.lseq uint64 15) : BE.table_inv_t U64 15ul 16ul =
  fun a table ->
    point_eval_lseq a = SG.point_mul_lambda (point_eval_lseq q) /\
    (forall (j:nat{j < 16}).
      PT.precomp_table_inv 15ul 0ul PM.mk_k256_concrete_ops q 16ul table j)

// This function returns [r_small]([lambda]Q)
// using a precomputed table [0; Q; 2Q; ...; 15Q]
inline_for_extraction noextract
val lprecomp_get_consttime_lambda:
  q:Ghost.erased (LSeq.lseq uint64 15){point_inv_lseq q} ->
  BE.pow_a_to_small_b_st U64 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul (table1_inv_precomp q)

let lprecomp_get_consttime_lambda q ctx lambda_q table1 r_small res =
  let h0 = ST.get () in
  assert (table1_inv_precomp q lambda_q (as_seq h0 table1));
  // table1.[r_small] = [r_small]Q
  BE.lprecomp_get_consttime 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul ctx q table1 r_small res;
  let h1 = ST.get () in
  assert (point_eval h1 res == SE.pow S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small));
  point_mul_lambda_inplace res;
  let h2 = ST.get () in
  assert (point_eval h2 res == SG.point_mul_lambda (point_eval h1 res));
  // GLV lemma
  assume (point_eval h2 res ==
    SE.pow S.mk_k256_concrete_ops (point_eval_lseq lambda_q) (v r_small))


inline_for_extraction noextract
val point_mul_split_lambda_table: out:point -> r1:qelem -> r2:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h out /\ live h r1 /\ live h r2 /\ live h q /\
    disjoint out q /\ disjoint out r1 /\ disjoint out r2 /\
    disjoint q r1 /\ disjoint q r2 /\
    point_inv h q /\
    qas_nat h r1 < S.q /\ qas_nat h r1 < pow2 129 /\
    qas_nat h r2 < S.q /\ qas_nat h r2 < pow2 129)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out ==
      SE.exp_double_fw S.mk_k256_concrete_ops (point_eval h0 q) 129
        (qas_nat h0 r1) (SG.point_mul_lambda (point_eval h0 q)) (qas_nat h0 r2) 4)

let point_mul_split_lambda_table out r1 r2 q =
  let h0 = ST.get () in
  push_frame ();
  let q2 = create_point () in
  point_mul_lambda q2 q; // q2 = [lambda]Q

  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = PM.mk_k256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 129ul in

  let table1 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) q table_len table1;

  ME.mk_lexp_double_fw_tables len ctx_len k l table_len
    (BE.table_inv_precomp len ctx_len k l table_len)
    (table1_inv_precomp (as_seq h0 q))
    (BE.lprecomp_get_consttime len ctx_len k l table_len)
    (lprecomp_get_consttime_lambda (as_seq h0 q))
    (null uint64) q bLen bBits r1 q2 r2 table1 table1 out;

  //ME.lexp_double_fw_vartime 15ul 0ul PM.mk_k256_concrete_ops 4ul (null uint64)
    //q 4ul 129ul r1 q2 r2 out;
  let h1 = ST.get () in
  assert (point_eval h1 out ==
      SE.exp_double_fw S.mk_k256_concrete_ops (point_eval h0 q) 129
        (qas_nat h0 r1) (SG.point_mul_lambda (point_eval h0 q)) (qas_nat h0 r2) 4);
  pop_frame ()


// TODO: share a table [0; P; 2P; ..; 15P] between P and ([lambda]P)
// [scalar]Q = [(r1 + r2 * lambda) % S.q]Q = [r1]Q + [r2]([lambda]Q)
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
  let r1 = create_qelem () in
  let r2 = create_qelem () in
  scalar_split_lambda r1 r2 scalar; // (r1 + r2 * lambda) % S.q = scalar
  point_mul_split_lambda_table out r1 r2 q;

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
