module Hacl.Impl.PCurves.PointMul.P256

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

open Spec.P256
open Hacl.Impl.PCurves.Constants.P256
open Hacl.Impl.PCurves.Bignum.P256
open Hacl.Impl.PCurves.Field.P256
open Hacl.Impl.PCurves.Finv.P256
open Hacl.Impl.PCurves.Qinv.P256
open Hacl.Impl.PCurves.Group.P256
open Hacl.Impl.PCurves.PrecompTable.P256
open Hacl.Impl.PCurves.PointMul

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module SPT256 = Hacl.Spec.PrecompBaseTable256
module ME = Hacl.Impl.MultiExponentiation
module BD = Hacl.Spec.Bignum.Definitions
module BE = Hacl.Impl.Exponentiation
module PT = Hacl.Impl.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
val point_mul: point_mul_t
let point_mul = point_mul_gen

let _ : squash (3ul *! 4ul == 12ul) = 
  assert_norm (v (3ul *! 4ul) == 12)

let _ : squash (16ul *! 12ul == 192ul) = 
  assert_norm (v (16ul *! 12ul) == 192)

let _ : squash (48ul *! 4ul == 192ul) = 
  assert_norm (v (48ul *! 4ul) == 192)

inline_for_extraction noextract
let cp = p256_params

inline_for_extraction noextract
let point = point #p256_params

inline_for_extraction noextract
let felem = felem #p256_params

inline_for_extraction noextract
let refl = refl #p256_params

inline_for_extraction noextract
let pt = p256_precomp_tables

inline_for_extraction noextract
let mk_pcurve_concrete_ops = mk_pcurve_concrete_ops #p256_params #p256_bn_ops #p256_curve_constants #p256_field_ops #p256_inv_sqrt #p256_point_ops

inline_for_extraction noextract
let table_inv_w4 = table_inv_w4 #p256_params #p256_bn_ops #p256_curve_constants #p256_field_ops #p256_inv_sqrt #p256_point_ops

inline_for_extraction noextract
let table_inv_w5 = table_inv_w5 #p256_params #p256_bn_ops #p256_curve_constants #p256_field_ops #p256_inv_sqrt #p256_point_ops

inline_for_extraction noextract
val point_mul_g_noalloc 
  : out:point -> scalar:felem
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
    LE.exp_four_fw S.mk_pcurve_comm_monoid g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4))

#push-options "--z3rlimit 3000 --split_queries always" 
let point_mul_g_noalloc out scalar q1 q2 q3 q4 =
  [@inline_let] let len = 3ul *! 4ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bBits = 64ul in
  [@inline_let] let bLen = 1ul in

  let h0 = ST.get () in
  recall_contents pt.basepoint_w4.table_w4 pt.basepoint_w4.table_lseq_w4;
  let h1 = ST.get () in
  pt.basepoint_w4.table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q1) (as_seq h1 pt.basepoint_w4.table_w4));

  recall_contents pt.g_pow2_64_w4.table_w4 pt.g_pow2_64_w4.table_lseq_w4;
  let h1 = ST.get () in
  pt.g_pow2_64_w4.table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q2) (as_seq h1 pt.g_pow2_64_w4.table_w4));

  recall_contents pt.g_pow2_128_w4.table_w4 pt.g_pow2_128_w4.table_lseq_w4;
  let h1 = ST.get () in
  pt.g_pow2_128_w4.table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q3) (as_seq h1 pt.g_pow2_128_w4.table_w4));

  recall_contents pt.g_pow2_192_w4.table_w4 pt.g_pow2_192_w4.table_lseq_w4;
  let h1 = ST.get () in
  pt.g_pow2_192_w4.table_lemma_w4 ();
  assert (table_inv_w4 (as_seq h1 q4) (as_seq h1 pt.g_pow2_192_w4.table_w4));

  let r1 = sub scalar 0ul bLen in
  let r2 = sub scalar bLen bLen in
  let r3 = sub scalar (2ul*!bLen) bLen in
  let r4 = sub scalar (3ul*!bLen) bLen in
  SPT256.lemma_decompose_nat256_as_four_u64_lbignum (as_seq h0 scalar);

  (* Annoying annotations to make F* prove the function call *)
  let buf_null: lbuffer uint64 ctx_len = null uint64 in
  let buf_q1 : lbuffer uint64 len = q1 in
  let buf_q2 : lbuffer uint64 len = q2 in
  let buf_q3 : lbuffer uint64 len = q3 in
  let buf_q4 : lbuffer uint64 len = q4 in
  let buf_base : clbuffer uint64 (table_len *! len) =
      to_const pt.basepoint_w4.table_w4 in
  let buf64 : clbuffer uint64 (table_len *! len) =
      to_const pt.g_pow2_64_w4.table_w4 in
  let buf128 : clbuffer uint64 (table_len *! len) =
      to_const pt.g_pow2_128_w4.table_w4 in
  let buf192 : clbuffer uint64 (table_len *! len) =
      to_const pt.g_pow2_192_w4.table_w4 in
  let buf_out : lbuffer uint64 len = out in
  (* End annoying annotations *)
  
  ME.mk_lexp_four_fw_tables len ctx_len k l table_len
    table_inv_w4 table_inv_w4 table_inv_w4 table_inv_w4
    pt.precomp_get_consttime
    pt.precomp_get_consttime
    pt.precomp_get_consttime
    pt.precomp_get_consttime
    buf_null buf_q1 bLen bBits r1 buf_q2 r2 buf_q3 r3 buf_q4 r4
    buf_base buf64 buf128 buf192
    buf_out
#pop-options

noextract
val lemma_exp_four_fw_local: b:BD.lbignum U64 4{BD.bn_v b < S.order} ->
  Lemma (
    let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v b) in
    LE.exp_four_fw S.mk_pcurve_comm_monoid g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 ==
    S.to_aff_point (S.point_mul_g (BD.bn_v b)))

let lemma_exp_four_fw_local b =
  let cm = S.mk_pcurve_comm_monoid in
  let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v b) in
  let res = LE.exp_four_fw cm g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 in
  assert (res == SPT256.exp_as_exp_four_nat256_precomp cm g_aff (BD.bn_v b));
  SPT256.lemma_point_mul_base_precomp4 cm g_aff (BD.bn_v b);
  assert (res == LE.pow cm g_aff (BD.bn_v b));
  SE.exp_fw_lemma S.mk_pcurve_concrete_ops S.base_point 256 (BD.bn_v b) 4;
  LE.exp_fw_lemma cm g_aff 256 (BD.bn_v b) 4;
  assert (S.to_aff_point (S.point_mul_g (BD.bn_v b)) == LE.pow cm g_aff (BD.bn_v b))

noextract inline_for_extraction
val point_mul_g_gen: point_mul_g_t


#push-options "--z3rlimit 150"
let point_mul_g_gen res scalar =
  push_frame ();
  let h0 = ST.get () in
  let q1 = create_point #p256_params in
  make_base_point q1;
  let q2 = pt.mk_proj_g_pow2_64.mk_proj_g_pow2 () in
  let q3 = pt.mk_proj_g_pow2_128.mk_proj_g_pow2 () in
  let q4 = pt.mk_proj_g_pow2_192.mk_proj_g_pow2 () in
  pt.mk_proj_g_pow2_64.proj_g_pow2_lseq_lemma ();
  pt.mk_proj_g_pow2_128.proj_g_pow2_lseq_lemma ();
  pt.mk_proj_g_pow2_192.proj_g_pow2_lseq_lemma ();
  point_mul_g_noalloc res scalar q1 q2 q3 q4;
  LowStar.Ignore.ignore q1;
  LowStar.Ignore.ignore q2;
  LowStar.Ignore.ignore q3;
  LowStar.Ignore.ignore q4;
  lemma_exp_four_fw_local (as_seq h0 scalar);
  pop_frame ()
#pop-options

//-------------------------

inline_for_extraction noextract
val point_mul_g_double_vartime_noalloc :
    out:point
  -> scalar1:felem -> q1:point
  -> scalar2:felem -> q2:point
  -> table2:lbuffer uint64 (32ul *! 3ul *! p256_params.bn_limbs) ->
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

#push-options "--z3rlimit 800 --split_queries always --admit_smt_queries true"
let point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2 =
  [@inline_let] let len = 3ul *! 4ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 64ul in
  assert_norm (pow2 (v l) == v table_len);
  let h0 = ST.get () in
  recall_contents pt.basepoint_w5.table_w5 pt.basepoint_w5.table_lseq_w5;
  let h1 = ST.get () in
  pt.basepoint_w5.table_lemma_w5 ();
  assert (table_inv_w5 (as_seq h1 q1) (as_seq h1 pt.basepoint_w5.table_w5));
  assert (table_inv_w5 (as_seq h1 q2) (as_seq h1 table2));
  ME.mk_lexp_double_fw_tables len ctx_len k l table_len
    table_inv_w5 table_inv_w5
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (null uint64) q1 bLen bBits scalar1 q2 scalar2
    (to_const pt.basepoint_w5.table_w5) (to_const table2) out;
  SE.exp_double_fw_lemma S.mk_pcurve_concrete_ops
    (from_mont_point (as_point_nat h0 q1)) cp.bits (as_nat h0 scalar1)
    (from_mont_point (as_point_nat h0 q2)) (as_nat h0 scalar2) 5
#pop-options

noextract inline_for_extraction
val point_mul_double_g_gen : point_mul_double_g_t

#push-options "--z3rlimit 150"
let point_mul_double_g_gen res scalar1 scalar2 q2 =
  push_frame ();
  [@inline_let] let len = 3ul *! cp.bn_limbs in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 5 == v table_len);

  let q1 = create_point #cp in
  make_base_point q1;

  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) q2 table_len table2;
  let h = ST.get () in
  assert (table_inv_w5 (as_seq h q2) (as_seq h table2));
  point_mul_g_double_vartime_noalloc res scalar1 q1 scalar2 q2 table2;
  pop_frame ()
#pop-options

[@CInline]
val point_mul_g: point_mul_g_t
let point_mul_g = point_mul_g_gen

[@CInline]
val point_mul_double_g: point_mul_double_g_t
let point_mul_double_g = point_mul_double_g_gen

inline_for_extraction
instance p256_point_mul_ops : point_mul_ops = {
  point_mul;
  point_mul_g;
  point_mul_double_g
}


