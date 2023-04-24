module Hacl.Impl.P256.PointMul

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Point

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module BD = Hacl.Spec.Bignum.Definitions

module S = Spec.P256
module SL = Spec.P256.Lemmas

include Hacl.Impl.P256.Group
include Hacl.P256.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let table_inv_w4 : BE.table_inv_t U64 12ul 16ul =
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
let table_inv_w5 : BE.table_inv_t U64 12ul 32ul =
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 (v l) == v table_len);
  BE.table_inv_precomp len ctx_len k l table_len


[@CInline]
let point_mul res scalar p =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_p256_concrete_ops
    (from_mont_point (as_point_nat h0 p)) 256 (as_nat h0 scalar) 4;
  BE.lexp_fw_consttime 12ul 0ul mk_p256_concrete_ops 4ul (null uint64) p 4ul 256ul scalar res


val precomp_get_consttime: BE.pow_a_to_small_b_st U64 12ul 0ul mk_p256_concrete_ops 4ul 16ul
    (BE.table_inv_precomp 12ul 0ul mk_p256_concrete_ops 4ul 16ul)
[@CInline]
let precomp_get_consttime ctx a table bits_l tmp =
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in

  BE.lprecomp_get_consttime len ctx_len k l table_len ctx a table bits_l tmp


inline_for_extraction noextract
val point_mul_g_noalloc: out:point -> scalar:felem
  -> q1:point -> q2:point
  -> q3:point -> q4:point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ live h q1 /\
    live h q2 /\ live h q3 /\ live h q4 /\
    disjoint out scalar /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out q3 /\ disjoint out q4 /\
    disjoint q1 q2 /\ disjoint q1 q3 /\ disjoint q1 q4 /\
    disjoint q2 q3 /\ disjoint q2 q4 /\ disjoint q3 q4 /\
    as_nat h scalar < S.order /\
    point_inv h q1 /\ refl (as_seq h q1) == g_aff /\
    point_inv h q2 /\ refl (as_seq h q2) == g_pow2_64 /\
    point_inv h q3 /\ refl (as_seq h q3) == g_pow2_128 /\
    point_inv h q4 /\ refl (as_seq h q4) == g_pow2_192)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
   (let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (as_nat h0 scalar) in
    S.to_aff_point (from_mont_point (as_point_nat h1 out)) ==
    LE.exp_four_fw S.mk_p256_comm_monoid g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4))

let point_mul_g_noalloc out scalar q1 q2 q3 q4 =
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 1ul in
  [@inline_let] let bBits = 64ul in

  let h0 = ST.get () in
  recall_contents precomp_basepoint_table_w4 precomp_basepoint_table_lseq_w4;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q1) (as_seq h1 precomp_basepoint_table_w4));

  recall_contents precomp_g_pow2_64_table_w4 precomp_g_pow2_64_table_lseq_w4;
  let h1 = ST.get () in
  precomp_g_pow2_64_table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q2) (as_seq h1 precomp_g_pow2_64_table_w4));

  recall_contents precomp_g_pow2_128_table_w4 precomp_g_pow2_128_table_lseq_w4;
  let h1 = ST.get () in
  precomp_g_pow2_128_table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q3) (as_seq h1 precomp_g_pow2_128_table_w4));

  recall_contents precomp_g_pow2_192_table_w4 precomp_g_pow2_192_table_lseq_w4;
  let h1 = ST.get () in
  precomp_g_pow2_192_table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q4) (as_seq h1 precomp_g_pow2_192_table_w4));

  let r1 = sub scalar 0ul 1ul in
  let r2 = sub scalar 1ul 1ul in
  let r3 = sub scalar 2ul 1ul in
  let r4 = sub scalar 3ul 1ul in
  SPT256.lemma_decompose_nat256_as_four_u64_lbignum (as_seq h0 scalar);

  ME.mk_lexp_four_fw_tables len ctx_len k l table_len
    table_inv_w4 table_inv_w4 table_inv_w4 table_inv_w4
    precomp_get_consttime
    precomp_get_consttime
    precomp_get_consttime
    precomp_get_consttime
    (null uint64) q1 bLen bBits r1 q2 r2 q3 r3 q4 r4
    (to_const precomp_basepoint_table_w4)
    (to_const precomp_g_pow2_64_table_w4)
    (to_const precomp_g_pow2_128_table_w4)
    (to_const precomp_g_pow2_192_table_w4)
    out


val lemma_exp_four_fw_local: b:BD.lbignum U64 4{BD.bn_v b < S.order} ->
  Lemma (let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v b) in
    LE.exp_four_fw S.mk_p256_comm_monoid g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 ==
    S.to_aff_point (S.point_mul_g (BD.bn_v b)))

let lemma_exp_four_fw_local b =
  let cm = S.mk_p256_comm_monoid in
  let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v b) in
  let res = LE.exp_four_fw cm g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 in
  assert (res == SPT256.exp_as_exp_four_nat256_precomp cm g_aff (BD.bn_v b));
  SPT256.lemma_point_mul_base_precomp4 cm g_aff (BD.bn_v b);
  assert (res == LE.pow cm g_aff (BD.bn_v b));
  SE.exp_fw_lemma S.mk_p256_concrete_ops S.base_point 256 (BD.bn_v b) 4;
  LE.exp_fw_lemma cm g_aff 256 (BD.bn_v b) 4;
  assert (S.to_aff_point (S.point_mul_g (BD.bn_v b)) == LE.pow cm g_aff (BD.bn_v b))


[@CInline]
let point_mul_g res scalar =
  push_frame ();
  let h0 = ST.get () in
  let q1 = create_point () in
  make_base_point q1;
  let q2 = mk_proj_g_pow2_64 () in
  let q3 = mk_proj_g_pow2_128 () in
  let q4 = mk_proj_g_pow2_192 () in
  proj_g_pow2_64_lseq_lemma ();
  proj_g_pow2_128_lseq_lemma ();
  proj_g_pow2_192_lseq_lemma ();
  point_mul_g_noalloc res scalar q1 q2 q3 q4;
  lemma_exp_four_fw_local (as_seq h0 scalar);
  pop_frame ()

//-------------------------

inline_for_extraction noextract
val point_mul_g_double_vartime_noalloc:
    out:point
  -> scalar1:felem -> q1:point
  -> scalar2:felem -> q2:point
  -> table2:lbuffer uint64 (32ul *! 12ul) ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\ live h table2 /\

    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out table2 /\

    as_nat h scalar1 < S.order /\ as_nat h scalar2 < S.order /\
    point_inv h q1 /\ from_mont_point (as_point_nat h q1) == S.base_point /\
    point_inv h q2 /\ table_inv_w5 (as_seq h q2) (as_seq h table2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    refl (as_seq h1 out) ==
    S.to_aff_point (S.point_mul_double_g
      (as_nat h0 scalar1) (as_nat h0 scalar2) (from_mont_point (as_point_nat h0 q2))))

let point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2 =
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
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

  SE.exp_double_fw_lemma S.mk_p256_concrete_ops
    (from_mont_point (as_point_nat h0 q1)) 256 (as_nat h0 scalar1)
    (from_mont_point (as_point_nat h0 q2)) (as_nat h0 scalar2) 5


[@CInline]
let point_mul_double_g res scalar1 scalar2 q2 =
  push_frame ();
  [@inline_let] let len = 12ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_p256_concrete_ops in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 5 == v table_len);

  let q1 = create_point () in
  make_base_point q1;

  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) q2 table_len table2;
  let h = ST.get () in
  assert (table_inv_w5 (as_seq h q2) (as_seq h table2));
  point_mul_g_double_vartime_noalloc res scalar1 q1 scalar2 q2 table2;
  pop_frame ()
