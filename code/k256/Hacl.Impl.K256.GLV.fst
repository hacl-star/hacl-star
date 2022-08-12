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

(**
  Representing a scalar k as (r1 + r2 * lambda) mod S.q,
  s.t. r1 and r2 are ~128 bits long
*)

inline_for_extraction noextract
val scalar_split_lambda_g1g2 (tmp1 tmp2 r1 r2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h r1 /\ live h r2 /\
    live h tmp1 /\ live h tmp2 /\
    disjoint k r1 /\ disjoint k r2 /\ disjoint r1 r2 /\
    disjoint tmp1 r1 /\ disjoint tmp1 r2 /\ disjoint tmp1 k /\
    disjoint tmp2 r1 /\ disjoint tmp2 r2 /\ disjoint tmp2 k /\
    disjoint tmp1 tmp2 /\ qas_nat h k < S.q)
  (ensures  fun h0 _ h1 ->
    modifies (loc r1 |+| loc r2 |+| loc tmp1 |+| loc tmp2) h0 h1 /\
   (let r1 = qas_nat h1 r1 in let r2 = qas_nat h1 r2 in
    r1 < S.q /\ r1 = SG.qmul_shift_384 (qas_nat h0 k) SG.g1 /\
    r2 < S.q /\ r2 = SG.qmul_shift_384 (qas_nat h0 k) SG.g2))

let scalar_split_lambda_g1g2 tmp1 tmp2 r1 r2 k =
  make_g1 tmp1; // tmp1 = g1
  make_g2 tmp2; // tmp2 = g2
  qmul_shift_384 r1 k tmp1; // r1 = c1 = qmul_shift_384 k g1
  qmul_shift_384 r2 k tmp2; // r2 = c2 = qmul_shift_384 k g2
  let h0 = ST.get () in
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp1);
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp2);
  assert (qas_nat h0 r1 < S.q /\ qas_nat h0 r2 < S.q)


// k = (r1 + lambda * k2) % S.q
val scalar_split_lambda (r1 r2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h r1 /\ live h r2 /\
    disjoint k r1 /\ disjoint k r2 /\ disjoint r1 r2 /\
    qas_nat h k < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc r1 |+| loc r2) h0 h1 /\
   (let r1_s, r2_s = SG.scalar_split_lambda (qas_nat h0 k) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s))

[@CInline]
let scalar_split_lambda r1 r2 k =
  push_frame ();
  let tmp1 = create_qelem () in
  let tmp2 = create_qelem () in
  scalar_split_lambda_g1g2 tmp1 tmp2 r1 r2 k;

  make_minus_b1 tmp1; // tmp1 = minus_b1
  make_minus_b2 tmp2; // tmp2 = minus_b2
  qmul r1 r1 tmp1; // r1 = c1 = c1 * minus_b1
  qmul r2 r2 tmp2; // r2 = c2 = c2 * minus_b2

  make_minus_lambda tmp1; // tmp1 = minus_lambda
  qadd r2 r1 r2; // r2 = r2 = c1 + c2
  qmul tmp2 r2 tmp1; // tmp2 = r2 * minus_lambda
  qadd r1 k tmp2; // r1 = r1 = k + r2 * minus_lambda
  pop_frame ()


(**
 Fast computation of [lambda]P as (beta * px, py, pz) in projective coordinates
*)

// [lambda]P = (beta * px, py, pz)
val point_mul_lambda: res:point -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ eq_or_disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 p))

[@CInline]
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
val point_mul_lambda_inplace: res:point -> Stack unit
  (requires fun h ->
    live h res /\ point_inv h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 res))

[@CInline]
let point_mul_lambda_inplace res =
  push_frame ();
  let rx, ry, rz = getx res, gety res, getz res in
  let beta = create_felem () in
  make_beta beta;
  fmul rx beta rx;
  pop_frame ()


(**
 Fast computation of [scalar]Q in projective coordinates
*)

inline_for_extraction noextract
val point_mul_lambda_and_split_lambda:
  r1:qelem -> r2:qelem -> lambda_q:point -> scalar:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h lambda_q /\ live h scalar /\ live h q /\
    disjoint r1 r2 /\ disjoint r1 lambda_q /\ disjoint r1 scalar /\ disjoint r1 q /\
    disjoint r2 lambda_q /\ disjoint r2 scalar /\ disjoint r2 q /\
    disjoint lambda_q scalar /\ disjoint lambda_q q /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures fun h0 _ h1 -> modifies (loc r1 |+| loc r2 |+| loc lambda_q) h0 h1 /\
    point_inv h1 lambda_q /\
    point_eval h1 lambda_q == SG.point_mul_lambda (point_eval h0 q) /\
   (let r1_s, r2_s = SG.scalar_split_lambda (qas_nat h0 scalar) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s))

let point_mul_lambda_and_split_lambda r1 r2 lambda_q scalar q =
  scalar_split_lambda r1 r2 scalar; // (r1 + r2 * lambda) % S.q = scalar
  point_mul_lambda lambda_q q // lambda_q = [lambda]Q


inline_for_extraction noextract
val point_negate_conditional_vartime: p:point -> is_negate:bool -> Stack unit
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\
    point_eval h1 p == SG.point_negate_cond (point_eval h0 p) is_negate)

let point_negate_conditional_vartime p is_negate =
  if is_negate then point_negate p p


inline_for_extraction noextract
val negate_point_and_scalar_cond_vartime: k:qelem -> p:point -> Stack bool
  (requires fun h ->
    live h k /\ live h p /\ disjoint k p /\
    qas_nat h k < S.q /\ point_inv h p)
  (ensures  fun h0 b h1 -> modifies (loc k |+| loc p) h0 h1 /\
    b == SG.scalar_is_high (qas_nat h0 k) /\ point_inv h1 p /\
    (let k_s, p_s = SG.negate_point_and_scalar_cond (qas_nat h0 k) (point_eval h0 p) in
    qas_nat h1 k == k_s /\ point_eval h1 p == p_s))

let negate_point_and_scalar_cond_vartime k p =
  let b = is_qelem_le_q_halved_vartime k in
  [@inline_let] let if_high = not b in
  qnegate_conditional_vartime k if_high;
  point_negate_conditional_vartime p if_high;
  if_high


inline_for_extraction noextract
val ecmult_endo_split:
    r1:qelem -> r2:qelem
  -> q1:point -> q2:point
  -> scalar:qelem -> q:point -> Stack (bool & bool)
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h q1 /\
    live h q2 /\ live h scalar /\ live h q /\
    disjoint r1 r2 /\ disjoint r1 q1 /\ disjoint r1 q2 /\
    disjoint r1 scalar /\ disjoint r1 q /\ disjoint r2 q1 /\
    disjoint r2 q2 /\ disjoint r2 scalar /\ disjoint r2 q /\
    disjoint q1 q2 /\ disjoint q1 scalar /\ disjoint q1 q /\
    disjoint q2 scalar /\ disjoint q2 q /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures fun h0 (is_high1, is_high2) h1 ->
    modifies (loc r1 |+| loc r2 |+| loc q1 |+| loc q2) h0 h1 /\
    point_inv h1 q1 /\ point_inv h1 q2 /\
   (let r1_s0, r2_s0 = SG.scalar_split_lambda (qas_nat h0 scalar) in
    let r1_s, q1_s, r2_s, q2_s = SG.ecmult_endo_split (qas_nat h0 scalar) (point_eval h0 q) in
    qas_nat h1 r1 == r1_s /\ point_eval h1 q1 == q1_s /\
    qas_nat h1 r2 == r2_s /\ point_eval h1 q2 == q2_s /\
    is_high1 == SG.scalar_is_high r1_s0 /\
    is_high2 == SG.scalar_is_high r2_s0))

let ecmult_endo_split r1 r2 q1 q2 scalar q =
  // modifies r1, r2, q2 s.t. r1 + r2 * lambda = scalar /\ q2 = [lambda]q
  point_mul_lambda_and_split_lambda r1 r2 q2 scalar q;
  copy_point q1 q; // q1 = q
  // modifies r1, q1
  let is_high1 = negate_point_and_scalar_cond_vartime r1 q1 in
  // modifies r2, q2
  let is_high2 = negate_point_and_scalar_cond_vartime r2 q2 in
  is_high1, is_high2

//----------------------------------------

inline_for_extraction noextract
let table_neg_inv_precomp
  (q:LSeq.lseq uint64 15) (is_negate:bool) : BE.table_inv_t U64 15ul 16ul =
  fun a table ->
    point_eval_lseq a == SG.point_negate_cond (point_eval_lseq q) is_negate /\
    (forall (j:nat{j < 16}).
      PT.precomp_table_inv 15ul 0ul PM.mk_k256_concrete_ops q 16ul table j)

// This function returns [r_small]Q or [r_small](-Q)
// using a precomputed table [0; Q; 2Q; ...; 15Q]
inline_for_extraction noextract
val lprecomp_get_vartime_neg:
    q:Ghost.erased (LSeq.lseq uint64 15){point_inv_lseq q} -> is_negate:bool ->
  BE.pow_a_to_small_b_st U64 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul
    (table_neg_inv_precomp q is_negate)

let lprecomp_get_vartime_neg q is_negate ctx lambda_q table r_small res =
  let h0 = ST.get () in
  assert (table_neg_inv_precomp q is_negate lambda_q (as_seq h0 table));
  // table.[r_small] = [r_small]Q
  BE.lprecomp_get_vartime 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul ctx q table r_small res;
  let h1 = ST.get () in
  assert (point_eval h1 res == SE.pow S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small));
  point_negate_conditional_vartime res is_negate;
  let h2 = ST.get () in
  assert (point_eval h2 res == SG.point_negate_cond (point_eval h1 res) is_negate);
  // -[r_small]Q = [r_small](-Q)
  assume (point_eval h2 res ==
    SE.pow S.mk_k256_concrete_ops
      (SG.point_negate_cond (point_eval_lseq q) is_negate) (v r_small))


inline_for_extraction noextract
let table_lambda_neg_inv_precomp
  (q:LSeq.lseq uint64 15) (is_negate:bool) : BE.table_inv_t U64 15ul 16ul =
  fun a table ->
    point_eval_lseq a ==
      SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq q)) is_negate /\
    (forall (j:nat{j < 16}).
      PT.precomp_table_inv 15ul 0ul PM.mk_k256_concrete_ops q 16ul table j)


// This function returns [r_small]([lambda]Q) or [r_small](-[lambda]Q)
// using a precomputed table [0; Q; 2Q; ...; 15Q]
inline_for_extraction noextract
val lprecomp_get_vartime_lambda_neg:
    q:Ghost.erased (LSeq.lseq uint64 15){point_inv_lseq q} -> is_negate:bool ->
  BE.pow_a_to_small_b_st U64 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul
    (table_lambda_neg_inv_precomp q is_negate)

let lprecomp_get_vartime_lambda_neg q is_negate ctx lambda_q table r_small res =
  let h0 = ST.get () in
  assert (table_lambda_neg_inv_precomp q is_negate lambda_q (as_seq h0 table));
  // table.[r_small] = [r_small]Q
  BE.lprecomp_get_vartime 15ul 0ul PM.mk_k256_concrete_ops 4ul 16ul ctx q table r_small res;
  let h1 = ST.get () in
  assert (point_eval h1 res == SE.pow S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small));
  // -[r_small]Q = [r_small](-Q)
  point_negate_conditional_vartime res is_negate;
  let h2 = ST.get () in
  assert (point_eval h2 res == SG.point_negate_cond (point_eval h1 res) is_negate);
  point_mul_lambda_inplace res;
  let h3 = ST.get () in
  assert (point_eval h3 res == SG.point_mul_lambda (point_eval h2 res));
  assume (point_eval h3 res ==
    SE.pow S.mk_k256_concrete_ops
      (SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq q)) is_negate) (v r_small))

//------------------------------

inline_for_extraction noextract
val point_mul_split_lambda_table:
  out:point -> r1:qelem -> q1:point -> r2:qelem -> q2:point
  -> p:point -> is_negate1:bool -> is_negate2:bool -> Stack unit
  (requires fun h ->
    live h out /\ live h r1 /\ live h r2 /\
    live h q1 /\ live h q2 /\ live h p /\
    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out r1 /\ disjoint out r2 /\ disjoint out p /\
    point_inv h q1 /\ point_inv h q2 /\ point_inv h p /\
    point_eval h q1 == SG.point_negate_cond (point_eval h p) is_negate1 /\
    point_eval h q2 == SG.point_negate_cond (SG.point_mul_lambda (point_eval h p)) is_negate2 /\
    qas_nat h r1 < S.q /\ qas_nat h r1 < pow2 128 /\
    qas_nat h r2 < S.q /\ qas_nat h r2 < pow2 128)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out ==
      SE.exp_double_fw S.mk_k256_concrete_ops
        (point_eval h0 q1) 128 (qas_nat h0 r1)
        (point_eval h0 q2) (qas_nat h0 r2) 4)

let point_mul_split_lambda_table out r1 q1 r2 q2 p is_negate1 is_negate2 =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = PM.mk_k256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 128ul in
  // ME.lexp_double_fw_vartime len ctx_len k l (null uint64) q1 bLen bBits r1 q2 r2 out

  let h0 = ST.get () in
  push_frame ();
  let table = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) p table_len table;
  admit();
  ME.mk_lexp_double_fw_tables len ctx_len k l table_len
    (table_neg_inv_precomp (as_seq h0 p) is_negate1)
    (table_lambda_neg_inv_precomp (as_seq h0 p) is_negate2)
    (lprecomp_get_vartime_neg (as_seq h0 p) is_negate1)
    (lprecomp_get_vartime_lambda_neg (as_seq h0 p) is_negate2)
    (null uint64) q1 bLen bBits r1 q2 r2 table table out;
  pop_frame ()


// [scalar]Q = [(r1 + r2 * lambda) % S.q]Q = [r1]Q + [r2]([lambda]Q)
val point_mul_split_lambda_vartime: out:point -> scalar:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ live h q /\
    disjoint out q /\ disjoint out scalar /\ disjoint q scalar /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul (qas_nat h0 scalar) (point_eval h0 q))

[@CInline]
let point_mul_split_lambda_vartime out scalar q =
  let h0 = ST.get () in
  push_frame ();
  let r1 = create_qelem () in
  let r2 = create_qelem () in
  let q1 = create_point () in
  let q2 = create_point () in
  let is_high1, is_high2 = ecmult_endo_split r1 r2 q1 q2 scalar q in
  let h = ST.get () in
  admit();
  point_mul_split_lambda_table out r1 q1 r2 q2 q is_high1 is_high2;
  pop_frame ()


// TODO: precompute a table [0; G; 2G; ..; 15G]?
val point_mul_g_split_lambda_vartime: out:point -> scalar:qelem -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ disjoint out scalar /\
    qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul_g (qas_nat h0 scalar))

[@CInline]
let point_mul_g_split_lambda_vartime out scalar =
  push_frame ();
  let g = create 15ul (u64 0) in
  PM.make_g g;
  point_mul_split_lambda_vartime out scalar g;
  pop_frame ()


(**
 Fast computation of [scalar1]Q1 + [scalar2]Q2 in projective coordinates
*)

inline_for_extraction noextract
val point_mul_double_split_lambda_table:
    out:point
  -> r1:qelem -> q1:point
  -> r2:qelem -> q2:point
  -> r3:qelem -> q3:point
  -> r4:qelem -> q4:point
  -> p1: point -> p2:point
  -> is_negate1:bool -> is_negate2:bool
  -> is_negate3:bool -> is_negate4:bool ->
  Stack unit
  (requires fun h ->
    live h out /\ live h r1 /\ live h r2 /\ live h r3 /\ live h r4 /\
    live h q1 /\ live h q2 /\ live h q3 /\ live h q4 /\ live h p1 /\ live h p2 /\
    eq_or_disjoint q1 q2 /\ eq_or_disjoint q1 q3 /\ eq_or_disjoint q1 q4 /\
    eq_or_disjoint q2 q3 /\ eq_or_disjoint q2 q4 /\ eq_or_disjoint q3 q4 /\
    disjoint out q1 /\ disjoint out q2 /\ disjoint out q3 /\ disjoint out q4 /\
    disjoint out r1 /\ disjoint out r2 /\ disjoint out r3 /\ disjoint out r4 /\
    disjoint out p1  /\ disjoint out p2 /\
    point_inv h q1 /\ point_inv h q2 /\ point_inv h q3 /\ point_inv h q4 /\
    point_inv h p1 /\ point_inv h p2 /\
    point_eval h q1==SG.point_negate_cond (point_eval h p1) is_negate1 /\
    point_eval h q2==SG.point_negate_cond (SG.point_mul_lambda (point_eval h p1)) is_negate2 /\
    point_eval h q3==SG.point_negate_cond (point_eval h p2) is_negate3 /\
    point_eval h q4==SG.point_negate_cond (SG.point_mul_lambda (point_eval h p2)) is_negate4 /\
    qas_nat h r1 < S.q /\ qas_nat h r1 < pow2 128 /\
    qas_nat h r2 < S.q /\ qas_nat h r2 < pow2 128 /\
    qas_nat h r3 < S.q /\ qas_nat h r3 < pow2 128 /\
    qas_nat h r4 < S.q /\ qas_nat h r4 < pow2 128)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out ==
      SE.exp_four_fw S.mk_k256_concrete_ops
        (point_eval h0 q1) 128 (qas_nat h0 r1)
        (point_eval h0 q2) (qas_nat h0 r2)
        (point_eval h0 q3) (qas_nat h0 r3)
        (point_eval h0 q4) (qas_nat h0 r4) 4)

let point_mul_double_split_lambda_table out r1 q1 r2 q2 r3 q3 r4 q4
  p1 p2 is_negate1 is_negate2 is_negate3 is_negate4 =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = PM.mk_k256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 128ul in
  //ME.lexp_four_fw_vartime len ctx_len k l (null uint64) q1 bLen bBits r1 q2 r2 q3 r3 q4 r4 out

  let h0 = ST.get () in
  push_frame ();
  let table1 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) p1 table_len table1;
  let h1 = ST.get () in
  assert (BE.table_inv_precomp len ctx_len k l table_len
    (as_seq h1 p1) (as_seq h1 table1));

  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) p2 table_len table2;
  let h2 = ST.get () in
  assert (BE.table_inv_precomp len ctx_len k l table_len
    (as_seq h2 p1) (as_seq h2 table1));
  assert (BE.table_inv_precomp len ctx_len k l table_len
    (as_seq h2 p2) (as_seq h2 table2));

  admit();
  ME.mk_lexp_four_fw_tables len ctx_len k l table_len
    (table_neg_inv_precomp (as_seq h0 p1) is_negate1)
    (table_lambda_neg_inv_precomp (as_seq h0 p1) is_negate2)
    (table_neg_inv_precomp (as_seq h0 p2) is_negate3)
    (table_lambda_neg_inv_precomp (as_seq h0 p2) is_negate4)
    (lprecomp_get_vartime_neg (as_seq h0 p1) is_negate1)
    (lprecomp_get_vartime_lambda_neg (as_seq h0 p1) is_negate2)
    (lprecomp_get_vartime_neg (as_seq h0 p2) is_negate3)
    (lprecomp_get_vartime_lambda_neg (as_seq h0 p2) is_negate4)
    (null uint64) q1 bLen bBits r1 q2 r2 q3 r3 q4 r4
    table1 table1 table2 table2 out;

  pop_frame ()


val point_mul_double_split_lambda_vartime:
  out:point -> scalar1:qelem -> q1:point -> scalar2:qelem -> q2:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\ live h scalar2 /\ live h q2 /\
    disjoint q1 out /\ disjoint q2 out /\ eq_or_disjoint q1 q2 /\
    disjoint scalar1 out /\ disjoint scalar2 out /\
    point_inv h q1 /\ point_inv h q2 /\
    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out ==
    S.point_mul_double
      (qas_nat h0 scalar1) (point_eval h0 q1)
      (qas_nat h0 scalar2) (point_eval h0 q2))

[@CInline]
let point_mul_double_split_lambda_vartime out scalar1 p1 scalar2 p2 =
  push_frame ();
  let r1 = create_qelem () in
  let r2 = create_qelem () in
  let r3 = create_qelem () in
  let r4 = create_qelem () in
  let q1 = create_point () in
  let q2 = create_point () in
  let q3 = create_point () in
  let q4 = create_point () in
  admit();
  let is_high1, is_high2 = ecmult_endo_split r1 r2 q1 q2 scalar1 p1 in
  let is_high3, is_high4 = ecmult_endo_split r3 r4 q3 q4 scalar2 p2 in
  point_mul_double_split_lambda_table out r1 q1 r2 q2 r3 q3 r4 q4
    p1 p2 is_high1 is_high2 is_high3 is_high4;
  pop_frame ()


val point_mul_g_double_split_lambda_vartime:
  out:point -> scalar1:qelem -> scalar2:qelem -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h scalar2 /\ live h q2 /\
    disjoint q2 out /\ disjoint out scalar1 /\ disjoint out scalar2 /\
    point_inv h q2 /\ qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out ==
    S.point_mul_double_g
      (qas_nat h0 scalar1) (qas_nat h0 scalar2) (point_eval h0 q2))

[@CInline]
let point_mul_g_double_split_lambda_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let g = create 15ul (u64 0) in
  PM.make_g g;
  point_mul_double_split_lambda_vartime out scalar1 g scalar2 q2;
  pop_frame ()
