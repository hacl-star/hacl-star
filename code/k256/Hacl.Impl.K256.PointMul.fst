module Hacl.Impl.K256.PointMul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable

module S = Spec.K256

open Hacl.K256.Scalar
open Hacl.Impl.K256.Point
include Hacl.Impl.K256.Group
include Hacl.K256.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let table_inv_w4 : BE.table_inv_t U64 15ul 16ul =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
let table_inv_w5 : BE.table_inv_t U64 15ul 32ul =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 (v l) == v table_len);
  BE.table_inv_precomp len ctx_len k l table_len


let point_mul out scalar q =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_k256_concrete_ops (point_eval h0 q) 256 (qas_nat h0 scalar) 4;
  BE.lexp_fw_consttime 15ul 0ul mk_k256_concrete_ops 4ul (null uint64) q 4ul 256ul scalar out


inline_for_extraction noextract
val point_mul_g_noalloc: out:point -> scalar:qelem -> g:point -> Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ live h g /\
    disjoint out scalar /\ disjoint out g /\ disjoint scalar g /\
    qas_nat h scalar < S.q /\
    point_inv h g /\ point_eval h g == S.g)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_eval h1 out) ==
    S.to_aff_point (S.point_mul_g (qas_nat h0 scalar)))

let point_mul_g_noalloc out scalar g =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 256ul in

  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_k256_concrete_ops (point_eval h0 g) 256 (qas_nat h0 scalar) 4;

  recall_contents precomp_basepoint_table_w4 precomp_basepoint_table_lseq_w4;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 g) (as_seq h1 precomp_basepoint_table_w4));
  assert (point_eval h1 g == S.g);

  BE.mk_lexp_fw_table len ctx_len k l table_len
    table_inv_w4
    (BE.lprecomp_get_consttime len ctx_len k l table_len)
    (null uint64) g bLen bBits scalar (to_const precomp_basepoint_table_w4) out


[@CInline]
let point_mul_g out scalar =
  push_frame ();
  let g = create 15ul (u64 0) in
  make_g g;
  point_mul_g_noalloc out scalar g;
  pop_frame ()

//-------------------------

inline_for_extraction noextract
val point_mul_g_double_vartime_noalloc:
    out:point
  -> scalar1:qelem -> q1:point
  -> scalar2:qelem -> q2:point
  -> table2:lbuffer uint64 (32ul *! 15ul) ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\ live h table2 /\

    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out table2 /\

    qas_nat h scalar1 < S.q /\ qas_nat h scalar2 < S.q /\
    point_inv h q1 /\ point_eval h q1 == S.g /\ point_inv h q2 /\
    table_inv_w5 (as_seq h q2) (as_seq h table2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_eval h1 out) ==
    S.to_aff_point (S.point_mul_double_g
      (qas_nat h0 scalar1) (qas_nat h0 scalar2) (point_eval h0 q2)))

let point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2 =
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 256ul in
  assert_norm (pow2 (v l) == v table_len);
  
  let h0 = ST.get () in
  recall_contents precomp_basepoint_table_w5 precomp_basepoint_table_lseq_w5;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma_w5 ();
  assert (table_inv_w5 (as_seq h1 q1) (as_seq h1 precomp_basepoint_table_w5));
  assert (table_inv_w5 (as_seq h1 q2) (as_seq h1 table2));

  ME.mk_lexp_double_fw_tables len ctx_len k l table_len
    table_inv_w5 table_inv_w5
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (null uint64) q1 bLen bBits scalar1 q2 scalar2
    (to_const precomp_basepoint_table_w5) (to_const table2) out;

  SE.exp_double_fw_lemma S.mk_k256_concrete_ops
    (point_eval h0 q1) 256 (qas_nat h0 scalar1)
    (point_eval h0 q2) (qas_nat h0 scalar2) 5


[@CInline]
let point_mul_g_double_vartime out scalar1 scalar2 q2 =
  push_frame ();
  [@inline_let] let len = 15ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_k256_concrete_ops in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 5 == v table_len);
  
  let q1 = create 15ul (u64 0) in
  make_g q1;

  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) q2 table_len table2;
  let h = ST.get () in
  assert (table_inv_w5 (as_seq h q2) (as_seq h table2));
  point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2;
  pop_frame ()
