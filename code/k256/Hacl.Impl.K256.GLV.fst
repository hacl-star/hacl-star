module Hacl.Impl.K256.GLV

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable

module S = Spec.K256
module SL = Spec.K256.Lemmas
module SG = Hacl.Spec.K256.GLV
module SGL = Hacl.Spec.K256.GLV.Lemmas
module PML = Hacl.Spec.K256.ECSM.Lemmas
module PM = Hacl.Impl.K256.PointMul

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point

open Hacl.Impl.K256.GLV.Constants
include Hacl.Impl.K256.Group
include Hacl.K256.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let _: squash(pow2 5 = 32) =
  assert_norm (pow2 5 = 32)

let _: squash(pow2 128 < S.q) =
  assert_norm (pow2 128 < S.q)


inline_for_extraction noextract
let table_inv_w5 : BE.table_inv_t U64 15ul 32ul =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
let table_neg_inv_precomp
  (q:LSeq.lseq uint64 15) (is_negate:bool) : BE.table_inv_t U64 15ul 32ul =
  fun a table ->
    point_eval_lseq a == SG.point_negate_cond (point_eval_lseq q) is_negate /\
    (forall (j:nat{j < 32}).
      PT.precomp_table_inv 15ul 0ul mk_k256_concrete_ops q 32ul table j)


// This function returns [r_small]Q or [r_small](-Q)
// using a precomputed table [0; Q; 2Q; ...; 15Q]
inline_for_extraction noextract
val lprecomp_get_vartime_neg:
    q:Ghost.erased (LSeq.lseq uint64 15){point_inv_lseq q} -> is_negate:bool ->
  BE.pow_a_to_small_b_st U64 15ul 0ul mk_k256_concrete_ops 5ul 32ul
    (table_neg_inv_precomp q is_negate)

let lprecomp_get_vartime_neg q is_negate ctx lambda_q table r_small res =
  let h0 = ST.get () in
  assert (table_neg_inv_precomp q is_negate lambda_q (as_seq h0 table));
  // table.[r_small] = [r_small]Q
  BE.lprecomp_get_vartime 15ul 0ul mk_k256_concrete_ops 5ul 32ul ctx q table r_small res;
  SE.pow_lemma S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small);
  let h1 = ST.get () in
  assert (S.to_aff_point (point_eval h1 res) ==
    S.to_aff_point (SE.pow S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small)));

  point_negate_conditional_vartime res is_negate;
  let h2 = ST.get () in
  assert (point_eval h2 res == SG.point_negate_cond (point_eval h1 res) is_negate);
  SL.to_aff_point_negate_lemma (point_eval h1 res);
  assert (S.to_aff_point (point_eval h2 res) ==
    SG.aff_point_negate_cond (S.to_aff_point (point_eval h1 res)) is_negate);

  // -[r_small]Q = [r_small](-Q)
  SGL.aff_point_negate_cond_pow_lemma is_negate (point_eval_lseq q) (v r_small);
  assert (S.to_aff_point (point_eval h2 res) ==
    LE.pow S.mk_k256_comm_monoid
      (S.to_aff_point (SG.point_negate_cond (point_eval_lseq q) is_negate)) (v r_small))


inline_for_extraction noextract
let table_lambda_neg_inv_precomp
  (q:LSeq.lseq uint64 15) (is_negate:bool) : BE.table_inv_t U64 15ul 32ul =
  fun a table ->
    point_eval_lseq a ==
      SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq q)) is_negate /\
    (forall (j:nat{j < 32}).
      PT.precomp_table_inv 15ul 0ul mk_k256_concrete_ops q 32ul table j)


// This function returns [r_small]([lambda]Q) or [r_small](-[lambda]Q)
// using a precomputed table [0; Q; 2Q; ...; 15Q]
inline_for_extraction noextract
val lprecomp_get_vartime_lambda_neg:
    q:Ghost.erased (LSeq.lseq uint64 15){point_inv_lseq q} -> is_negate:bool ->
  BE.pow_a_to_small_b_st U64 15ul 0ul mk_k256_concrete_ops 5ul 32ul
    (table_lambda_neg_inv_precomp q is_negate)

let lprecomp_get_vartime_lambda_neg q is_negate ctx lambda_q table r_small res =
  let h0 = ST.get () in
  assert (table_lambda_neg_inv_precomp q is_negate lambda_q (as_seq h0 table));
  // table.[r_small] = [r_small]Q
  BE.lprecomp_get_vartime 15ul 0ul mk_k256_concrete_ops 5ul 32ul ctx q table r_small res;
  SE.pow_lemma S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small);
  let h1 = ST.get () in
  assert (S.to_aff_point (point_eval h1 res) ==
    S.to_aff_point (SE.pow S.mk_k256_concrete_ops (point_eval_lseq q) (v r_small)));

  // -[r_small]Q = [r_small](-Q)
  point_negate_conditional_vartime res is_negate;
  let h2 = ST.get () in
  assert (point_eval h2 res == SG.point_negate_cond (point_eval h1 res) is_negate);
  SL.to_aff_point_negate_lemma (point_eval h1 res);
  assert (S.to_aff_point (point_eval h2 res) ==
    SG.aff_point_negate_cond (S.to_aff_point (point_eval h1 res)) is_negate);

  // [lambda]([r_small]Q) or [lambda]([r_small](-Q))
  point_mul_lambda_inplace res;
  let h3 = ST.get () in
  assert (point_eval h3 res == SG.point_mul_lambda (point_eval h2 res));
  SGL.lemma_glv (point_eval h2 res);
  assert (S.to_aff_point (point_eval h3 res) ==
    SG.aff_point_mul SG.lambda (S.to_aff_point (point_eval h2 res)));

  // [r_small]([lambda]Q) or [r_small](-[lambda]Q)
  SGL.aff_point_negate_cond_lambda_pow_lemma is_negate (point_eval_lseq q) (v r_small);
  assert (S.to_aff_point (point_eval h3 res) ==
    LE.pow S.mk_k256_comm_monoid
      (S.to_aff_point
        (SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq q)) is_negate)) (v r_small))

//------------------------------

inline_for_extraction noextract
val point_mul_g_double_split_lambda_table_noalloc:
    out:point
  -> table2:lbuffer uint64 (32ul *! 15ul)
  -> r1:qelem -> q1:point
  -> r2:qelem -> q2:point
  -> r3:qelem -> q3:point
  -> r4:qelem -> q4:point
  -> p1:point -> p2:point
  -> is_negate1:bool -> is_negate2:bool
  -> is_negate3:bool -> is_negate4:bool ->
  Stack unit
  (requires fun h ->
    live h out /\ live h table2 /\
    live h r1 /\ live h r2 /\ live h r3 /\ live h r4 /\
    live h q1 /\ live h q2 /\ live h q3 /\ live h q4 /\
    live h p1 /\ live h p2 /\

    eq_or_disjoint q1 q2 /\ eq_or_disjoint q1 q3 /\ eq_or_disjoint q1 q4 /\
    eq_or_disjoint q2 q3 /\ eq_or_disjoint q2 q4 /\ eq_or_disjoint q3 q4 /\
    disjoint out q1 /\ disjoint out q2 /\ disjoint out q3 /\ disjoint out q4 /\
    disjoint out r1 /\ disjoint out r2 /\ disjoint out r3 /\ disjoint out r4 /\
    disjoint out p1  /\ disjoint out p2 /\

    disjoint table2 out /\ disjoint table2 r1 /\ disjoint table2 r2 /\
    disjoint table2 r3 /\ disjoint table2 r4 /\  disjoint table2 p1 /\
    disjoint table2 p2 /\ disjoint table2 q1 /\ disjoint table2 q2 /\
    disjoint table2 q3 /\ disjoint table2 q4 /\

    point_inv h q1 /\ point_inv h q2 /\ point_inv h q3 /\ point_inv h q4 /\
    point_inv h p1 /\ point_inv h p2 /\
    point_eval h p1 == S.g /\
    point_eval h q1==SG.point_negate_cond (point_eval h p1) is_negate1 /\
    point_eval h q2==SG.point_negate_cond (SG.point_mul_lambda (point_eval h p1)) is_negate2 /\
    point_eval h q3==SG.point_negate_cond (point_eval h p2) is_negate3 /\
    point_eval h q4==SG.point_negate_cond (SG.point_mul_lambda (point_eval h p2)) is_negate4 /\
    qas_nat h r1 < S.q /\ qas_nat h r1 < pow2 128 /\
    qas_nat h r2 < S.q /\ qas_nat h r2 < pow2 128 /\
    qas_nat h r3 < S.q /\ qas_nat h r3 < pow2 128 /\
    qas_nat h r4 < S.q /\ qas_nat h r4 < pow2 128 /\
    table_inv_w5 (as_seq h p2) (as_seq h table2))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    refl (as_seq h1 out) ==
      LE.exp_four_fw S.mk_k256_comm_monoid
        (refl (as_seq h0 q1)) 128 (qas_nat h0 r1)
        (refl (as_seq h0 q2)) (qas_nat h0 r2)
        (refl (as_seq h0 q3)) (qas_nat h0 r3)
        (refl (as_seq h0 q4)) (qas_nat h0 r4) 5)

let point_mul_g_double_split_lambda_table_noalloc out table2 r1 q1 r2 q2 r3 q3 r4 q4 p1 p2
  is_negate1 is_negate2 is_negate3 is_negate4 =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 128ul in

  let h0 = ST.get () in
  recall_contents precomp_basepoint_table_w5 precomp_basepoint_table_lseq_w5;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma_w5 ();
  assert (table_inv_w5 (as_seq h1 p1) (as_seq h1 precomp_basepoint_table_w5));
  assert (table_inv_w5 (as_seq h1 p2) (as_seq h1 table2));

  assert (point_eval_lseq (as_seq h1 q1) ==
    SG.point_negate_cond (point_eval_lseq (as_seq h1 p1)) is_negate1);
  [@inline_let]
  let table_inv1 : BE.table_inv_t U64 len table_len =
    table_neg_inv_precomp (as_seq h0 p1) is_negate1 in
  assert (table_inv1 (as_seq h1 q1) (as_seq h1 precomp_basepoint_table_w5));

  assert (point_eval_lseq (as_seq h1 q2) ==
    SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq (as_seq h1 p1))) is_negate2);
  [@inline_let]
  let table_inv2 : BE.table_inv_t U64 len table_len =
    table_lambda_neg_inv_precomp (as_seq h0 p1) is_negate2 in
  assert (table_inv2 (as_seq h1 q2) (as_seq h1 precomp_basepoint_table_w5));

  assert (point_eval_lseq (as_seq h1 q3) ==
    SG.point_negate_cond (point_eval_lseq (as_seq h1 p2)) is_negate3);
  [@inline_let]
  let table_inv3 : BE.table_inv_t U64 len table_len =
    table_neg_inv_precomp (as_seq h0 p2) is_negate3 in
  assert (table_inv3 (as_seq h1 q3) (as_seq h1 table2));

  assert (point_eval_lseq (as_seq h1 q4) ==
    SG.point_negate_cond (SG.point_mul_lambda (point_eval_lseq (as_seq h1 p2))) is_negate4);
  [@inline_let]
  let table_inv4 : BE.table_inv_t U64 len table_len =
    table_lambda_neg_inv_precomp (as_seq h0 p2) is_negate4 in
  assert (table_inv4 (as_seq h1 q4) (as_seq h1 table2));

  ME.mk_lexp_four_fw_tables len ctx_len k l table_len
    table_inv1 table_inv2 table_inv3 table_inv4
    (lprecomp_get_vartime_neg (as_seq h0 p1) is_negate1)
    (lprecomp_get_vartime_lambda_neg (as_seq h0 p1) is_negate2)
    (lprecomp_get_vartime_neg (as_seq h0 p2) is_negate3)
    (lprecomp_get_vartime_lambda_neg (as_seq h0 p2) is_negate4)
    (null uint64) q1 bLen bBits r1 q2 r2 q3 r3 q4 r4
    (to_const precomp_basepoint_table_w5)
    (to_const precomp_basepoint_table_w5)
    (to_const table2) (to_const table2) out


val point_mul_g_double_split_lambda_table:
    out:point
  -> r1:qelem -> q1:point
  -> r2:qelem -> q2:point
  -> r3:qelem -> q3:point
  -> r4:qelem -> q4:point
  -> p1:point -> p2:point
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
    point_eval h p1 == S.g /\
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
    refl (as_seq h1 out) ==
      LE.exp_four_fw S.mk_k256_comm_monoid
        (refl (as_seq h0 q1)) 128 (qas_nat h0 r1)
        (refl (as_seq h0 q2)) (qas_nat h0 r2)
        (refl (as_seq h0 q3)) (qas_nat h0 r3)
        (refl (as_seq h0 q4)) (qas_nat h0 r4) 5)

[@CInline]
let point_mul_g_double_split_lambda_table out r1 q1 r2 q2 r3 q3 r4 q4
  p1 p2 is_negate1 is_negate2 is_negate3 is_negate4 =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let table_len = 32ul in

  let h0 = ST.get () in
  push_frame ();
  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) p2 table_len table2;
  point_mul_g_double_split_lambda_table_noalloc out table2 r1 q1 r2 q2 r3 q3 r4 q4
    p1 p2 is_negate1 is_negate2 is_negate3 is_negate4;
  let h1 = ST.get () in
  assert (modifies (loc out |+| loc table2) h0 h1);
  pop_frame ();
  let h2 = ST.get () in
  assert (modifies (loc out) h0 h2)


inline_for_extraction noextract
val point_mul_g_double_split_lambda_vartime_endo_split:
    r1:qelem -> q1:point
  -> r2:qelem -> q2:point
  -> r3:qelem -> q3:point
  -> r4:qelem -> q4:point
  -> scalar1:qelem -> scalar2:qelem
  -> p1:point -> p2:point ->
  Stack (bool & bool & bool & bool)
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h r3 /\ live h r4 /\
    live h q1 /\ live h q2 /\ live h q3 /\ live h q4 /\
    live h p1 /\ live h p2 /\ live h scalar1 /\ live h scalar2 /\

    disjoint r1 q1 /\ disjoint r1 r2 /\ disjoint r1 q2 /\ disjoint r1 r3 /\
    disjoint r1 q3 /\ disjoint r1 r4 /\ disjoint r1 q4 /\ disjoint r1 scalar1 /\
    disjoint r1 scalar2 /\ disjoint r1 p1 /\ disjoint r1 p2 /\

    disjoint q1 r2 /\ disjoint q1 q2 /\ disjoint q1 r3 /\ disjoint q1 q3 /\
    disjoint q1 r4 /\ disjoint q1 q4 /\ disjoint q1 scalar1 /\ disjoint q1 scalar2 /\
    disjoint q1 p1 /\ disjoint q1 p2 /\

    disjoint r2 q2 /\ disjoint r2 r3 /\ disjoint r2 q3 /\ disjoint r2 r4 /\
    disjoint r2 q4 /\ disjoint r2 scalar1 /\ disjoint r2 scalar2 /\ disjoint r2 p1 /\
    disjoint r2 p2 /\

    disjoint q2 r3 /\ disjoint q2 q3 /\ disjoint q2 r4 /\ disjoint q2 q4 /\
    disjoint q2 scalar1 /\ disjoint q2 scalar2 /\ disjoint q2 p1 /\ disjoint q2 p2 /\

    disjoint r3 q3 /\ disjoint r3 r4 /\ disjoint r3 q4 /\ disjoint r3 scalar1 /\
    disjoint r3 scalar2 /\ disjoint r3 p1 /\ disjoint r3 p2 /\

    disjoint q3 r4 /\ disjoint q3 q4 /\ disjoint q3 scalar1 /\ disjoint q3 scalar2 /\
    disjoint q3 p1 /\ disjoint q3 p2 /\

    disjoint r4 q4 /\ disjoint r4 scalar1 /\ disjoint r4 scalar2 /\ disjoint r4 p1 /\
    disjoint r4 p2 /\

    disjoint q4 scalar1 /\ disjoint q4 scalar2 /\ disjoint q4 p1 /\ disjoint q4 p2 /\

    point_inv h p1 /\ point_inv h p2 /\
    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures  fun h0 (is_high1, is_high2, is_high3, is_high4) h1 ->
    modifies (loc r1 |+| loc r2 |+| loc r3 |+| loc r4 |+|
      loc q1 |+| loc q2 |+| loc q3 |+| loc q4) h0 h1 /\

    point_inv h1 q1 /\ point_inv h1 q2 /\ point_inv h1 q3 /\ point_inv h1 q4 /\
   (let r1_s0, r2_s0 = SG.scalar_split_lambda (qas_nat h0 scalar1) in
    let r3_s0, r4_s0 = SG.scalar_split_lambda (qas_nat h0 scalar2) in
    let r1_s, q1_s, r2_s, q2_s = SG.ecmult_endo_split (qas_nat h0 scalar1) (point_eval h0 p1) in
    let r3_s, q3_s, r4_s, q4_s = SG.ecmult_endo_split (qas_nat h0 scalar2) (point_eval h0 p2) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s /\
    qas_nat h1 r3 == r3_s /\ qas_nat h1 r4 == r4_s /\
    point_eval h1 q1 == q1_s /\ point_eval h1 q2 == q2_s /\
    point_eval h1 q3 == q3_s /\ point_eval h1 q4 == q4_s /\
    is_high1 == S.scalar_is_high r1_s0 /\
    is_high2 == S.scalar_is_high r2_s0 /\
    is_high3 == S.scalar_is_high r3_s0 /\
    is_high4 == S.scalar_is_high r4_s0))

let point_mul_g_double_split_lambda_vartime_endo_split r1 q1 r2 q2 r3 q3 r4 q4
  scalar1 scalar2 p1 p2 =
  let is_high1, is_high2 = ecmult_endo_split r1 r2 q1 q2 scalar1 p1 in
  let is_high3, is_high4 = ecmult_endo_split r3 r4 q3 q4 scalar2 p2 in
  (is_high1, is_high2, is_high3, is_high4)


val check_ecmult_endo_split (r1 r2 r3 r4 : qelem) :
  Stack bool
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h r3 /\ live h r4)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b ==
      (qas_nat h0 r1 < pow2 128 &&
       qas_nat h0 r2 < pow2 128 &&
       qas_nat h0 r3 < pow2 128 &&
       qas_nat h0 r4 < pow2 128))

[@CInline]
let check_ecmult_endo_split r1 r2 r3 r4 =
  let b1 = is_qelem_lt_pow2_128_vartime r1 in
  let b2 = is_qelem_lt_pow2_128_vartime r2 in
  let b3 = is_qelem_lt_pow2_128_vartime r3 in
  let b4 = is_qelem_lt_pow2_128_vartime r4 in
  b1 && b2 && b3 && b4


inline_for_extraction noextract
val point_mul_g_double_split_lambda_vartime_noalloc:
    out:point
  -> r1:qelem -> q1:point
  -> r2:qelem -> q2:point
  -> r3:qelem -> q3:point
  -> r4:qelem -> q4:point
  -> scalar1:qelem -> scalar2:qelem
  -> p1:point -> p2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h r1 /\ live h r2 /\ live h r3 /\ live h r4 /\
    live h q1 /\ live h q2 /\ live h q3 /\ live h q4 /\
    live h p1 /\ live h p2 /\ live h scalar1 /\ live h scalar2 /\

    disjoint out r1 /\ disjoint out q1 /\ disjoint out r2 /\ disjoint out q2 /\
    disjoint out r3 /\ disjoint out q3 /\ disjoint out r4 /\ disjoint out q4 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out p1 /\ disjoint out p2 /\

    disjoint r1 q1 /\ disjoint r1 r2 /\ disjoint r1 q2 /\ disjoint r1 r3 /\
    disjoint r1 q3 /\ disjoint r1 r4 /\ disjoint r1 q4 /\ disjoint r1 scalar1 /\
    disjoint r1 scalar2 /\ disjoint r1 p1 /\ disjoint r1 p2 /\

    disjoint q1 r2 /\ disjoint q1 q2 /\ disjoint q1 r3 /\ disjoint q1 q3 /\
    disjoint q1 r4 /\ disjoint q1 q4 /\ disjoint q1 scalar1 /\ disjoint q1 scalar2 /\
    disjoint q1 p1 /\ disjoint q1 p2 /\

    disjoint r2 q2 /\ disjoint r2 r3 /\ disjoint r2 q3 /\ disjoint r2 r4 /\
    disjoint r2 q4 /\ disjoint r2 scalar1 /\ disjoint r2 scalar2 /\ disjoint r2 p1 /\
    disjoint r2 p2 /\

    disjoint q2 r3 /\ disjoint q2 q3 /\ disjoint q2 r4 /\ disjoint q2 q4 /\
    disjoint q2 scalar1 /\ disjoint q2 scalar2 /\ disjoint q2 p1 /\ disjoint q2 p2 /\

    disjoint r3 q3 /\ disjoint r3 r4 /\ disjoint r3 q4 /\ disjoint r3 scalar1 /\
    disjoint r3 scalar2 /\ disjoint r3 p1 /\ disjoint r3 p2 /\

    disjoint q3 r4 /\ disjoint q3 q4 /\ disjoint q3 scalar1 /\ disjoint q3 scalar2 /\
    disjoint q3 p1 /\ disjoint q3 p2 /\

    disjoint r4 q4 /\ disjoint r4 scalar1 /\ disjoint r4 scalar2 /\ disjoint r4 p1 /\
    disjoint r4 p2 /\

    disjoint q4 scalar1 /\ disjoint q4 scalar2 /\ disjoint q4 p1 /\ disjoint q4 p2 /\

    point_inv h p1 /\ point_inv h p2 /\ point_eval h p1 == S.g /\
    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc r1 |+| loc r2 |+| loc r3 |+| loc r4 |+|
    loc q1 |+| loc q2 |+| loc q3 |+| loc q4 |+| loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_eval h1 out) ==
    S.aff_point_add
      (S.aff_point_mul (qas_nat h0 scalar1) (S.to_aff_point (point_eval h0 p1)))
      (S.aff_point_mul (qas_nat h0 scalar2) (S.to_aff_point (point_eval h0 p2))))

let point_mul_g_double_split_lambda_vartime_noalloc out r1 q1 r2 q2 r3 q3 r4 q4
  scalar1 scalar2 p1 p2 =
  let h0 = ST.get () in
  let is_high1, is_high2, is_high3, is_high4 =
   point_mul_g_double_split_lambda_vartime_endo_split
     r1 q1 r2 q2 r3 q3 r4 q4 scalar1 scalar2 p1 p2 in
  let is_r1234_valid = check_ecmult_endo_split r1 r2 r3 r4 in
  if is_r1234_valid then
    point_mul_g_double_split_lambda_table out r1 q1 r2 q2 r3 q3 r4 q4
      p1 p2 is_high1 is_high2 is_high3 is_high4
  else
    PM.point_mul_g_double_vartime out scalar1 scalar2 p2;
  let h1 = ST.get () in
  assert (S.to_aff_point (point_eval h1 out) ==
    SGL.aff_proj_point_mul_double_split_lambda
      (qas_nat h0 scalar1) (point_eval h0 p1)
      (qas_nat h0 scalar2) (point_eval h0 p2));
  SGL.lemma_aff_proj_point_mul_double_split_lambda
    (qas_nat h0 scalar1) (point_eval h0 p1)
    (qas_nat h0 scalar2) (point_eval h0 p2)


inline_for_extraction noextract
val point_mul_g_double_split_lambda_vartime_noalloc_aux:
    out:point
  -> r1234:lbuffer uint64 16ul
  -> q1234:lbuffer uint64 60ul
  -> scalar1:qelem -> scalar2:qelem
  -> p1:point -> p2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h r1234 /\ live h q1234 /\
    live h p1 /\ live h p2 /\ live h scalar1 /\ live h scalar2 /\

    disjoint out r1234 /\ disjoint out q1234 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out p1 /\ disjoint out p2 /\

    disjoint r1234 q1234 /\ disjoint r1234 scalar1 /\ disjoint r1234 scalar2 /\
    disjoint r1234 p1 /\ disjoint r1234 p2 /\

    disjoint q1234 scalar1 /\ disjoint q1234 scalar2 /\ disjoint q1234 p1 /\ disjoint q1234 p2 /\

    point_inv h p1 /\ point_inv h p2 /\ point_eval h p1 == S.g /\
    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc r1234 |+| loc q1234 |+| loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_eval h1 out) ==
    S.aff_point_add
      (S.aff_point_mul (qas_nat h0 scalar1) (S.to_aff_point (point_eval h0 p1)))
      (S.aff_point_mul (qas_nat h0 scalar2) (S.to_aff_point (point_eval h0 p2))))

let point_mul_g_double_split_lambda_vartime_noalloc_aux out r1234 q1234 scalar1 scalar2 p1 p2 =
  let r1 = sub r1234 0ul 4ul in
  let r2 = sub r1234 4ul 4ul in
  let r3 = sub r1234 8ul 4ul in
  let r4 = sub r1234 12ul 4ul in

  let q1 = sub q1234 0ul 15ul in
  let q2 = sub q1234 15ul 15ul in
  let q3 = sub q1234 30ul 15ul in
  let q4 = sub q1234 45ul 15ul in
  point_mul_g_double_split_lambda_vartime_noalloc
    out r1 q1 r2 q2 r3 q3 r4 q4 scalar1 scalar2 p1 p2


inline_for_extraction noextract
val point_mul_g_double_split_lambda_vartime_alloc:
  out:point -> scalar1:qelem -> p1:point -> scalar2:qelem -> p2:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h p1 /\ live h scalar2 /\ live h p2 /\
    disjoint p1 out /\ disjoint p2 out /\ eq_or_disjoint p1 p2 /\
    disjoint scalar1 out /\ disjoint scalar2 out /\
    point_inv h p1 /\ point_inv h p2 /\ point_eval h p1 == S.g /\
    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_eval h1 out) ==
    S.aff_point_add
      (S.aff_point_mul (qas_nat h0 scalar1) (S.to_aff_point (point_eval h0 p1)))
      (S.aff_point_mul (qas_nat h0 scalar2) (S.to_aff_point (point_eval h0 p2))))

let point_mul_g_double_split_lambda_vartime_alloc out scalar1 p1 scalar2 p2 =
  push_frame ();
  let r1234 = create 16ul (u64 0) in
  let q1234 = create 60ul (u64 0) in
  point_mul_g_double_split_lambda_vartime_noalloc_aux out r1234 q1234 scalar1 scalar2 p1 p2;
  pop_frame ()


[@CInline]
let point_mul_g_double_split_lambda_vartime out scalar1 scalar2 p2 =
  let h0 = ST.get () in
  SE.exp_double_fw_lemma S.mk_k256_concrete_ops S.g 256
    (qas_nat h0 scalar1) (point_eval h0 p2) (qas_nat h0 scalar2) 5;
  LE.exp_double_fw_lemma S.mk_k256_comm_monoid
    (S.to_aff_point S.g) 256 (qas_nat h0 scalar1)
    (S.to_aff_point (point_eval h0 p2)) (qas_nat h0 scalar2) 5;
  push_frame ();
  let g = create 15ul (u64 0) in
  make_g g;
  point_mul_g_double_split_lambda_vartime_alloc out scalar1 g scalar2 p2;
  pop_frame ()
