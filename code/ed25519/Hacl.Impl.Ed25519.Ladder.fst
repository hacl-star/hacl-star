module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51

module BSeq = Lib.ByteSequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module BD = Hacl.Bignum.Definitions
module SD = Hacl.Spec.Bignum.Definitions

module S = Spec.Ed25519

open Hacl.Impl.Ed25519.PointConstants
include Hacl.Impl.Ed25519.Group
include Hacl.Ed25519.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let table_inv_w4 : BE.table_inv_t U64 20ul 16ul =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
let table_inv_w5 : BE.table_inv_t U64 20ul 32ul =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 (v l) = v table_len);
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
val convert_scalar: scalar:lbuffer uint8 32ul -> bscalar:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h -> live h scalar /\ live h bscalar /\ disjoint scalar bscalar)
  (ensures fun h0 _ h1 -> modifies (loc bscalar) h0 h1 /\
    BD.bn_v h1 bscalar == BSeq.nat_from_bytes_le (as_seq h0 scalar))

let convert_scalar scalar bscalar =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #U64 32 (as_seq h0 scalar);
  Hacl.Bignum.Convert.mk_bn_from_bytes_le true 32ul scalar bscalar


inline_for_extraction noextract
val point_mul_noalloc:
    out:point
  -> bscalar:lbuffer uint64 4ul
  -> q:point ->
  Stack unit
  (requires fun h ->
    live h bscalar /\ live h q /\ live h out /\
    disjoint q out /\ disjoint q bscalar /\ disjoint out bscalar /\
    F51.point_inv_t h q /\ F51.inv_ext_point (as_seq h q) /\
    BD.bn_v h bscalar < pow2 256)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_fw S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q)) 256 (BD.bn_v h0 bscalar) 4)

let point_mul_noalloc out bscalar q =
  BE.lexp_fw_consttime 20ul 0ul mk_ed25519_concrete_ops
    4ul (null uint64) q 4ul 256ul bscalar out


let point_mul out scalar q =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_ed25519_concrete_ops
    (F51.point_eval h0 q) 256 (BSeq.nat_from_bytes_le (as_seq h0 scalar)) 4;
  push_frame ();
  let bscalar = create 4ul (u64 0) in
  convert_scalar scalar bscalar;
  point_mul_noalloc out bscalar q;
  pop_frame ()


val precomp_get_consttime: BE.pow_a_to_small_b_st U64 20ul 0ul mk_ed25519_concrete_ops 4ul 16ul
    (BE.table_inv_precomp 20ul 0ul mk_ed25519_concrete_ops 4ul 16ul)
[@CInline]
let precomp_get_consttime ctx a table bits_l tmp =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in

  BE.lprecomp_get_consttime len ctx_len k l table_len ctx a table bits_l tmp


inline_for_extraction noextract
val point_mul_g_noalloc: out:point -> bscalar:lbuffer uint64 4ul
  -> q1:point -> q2:point
  -> q3:point -> q4:point ->
  Stack unit
  (requires fun h ->
    live h bscalar /\ live h out /\ live h q1 /\
    live h q2 /\ live h q3 /\ live h q4 /\
    disjoint out bscalar /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out q3 /\ disjoint out q4 /\
    disjoint q1 q2 /\ disjoint q1 q3 /\ disjoint q1 q4 /\
    disjoint q2 q3 /\ disjoint q2 q4 /\ disjoint q3 q4 /\
    BD.bn_v h bscalar < pow2 256 /\
    F51.linv (as_seq h q1) /\ refl (as_seq h q1) == g_aff /\
    F51.linv (as_seq h q2) /\ refl (as_seq h q2) == g_pow2_64 /\
    F51.linv (as_seq h q3) /\ refl (as_seq h q3) == g_pow2_128 /\
    F51.linv (as_seq h q4) /\ refl (as_seq h q4) == g_pow2_192)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.linv (as_seq h1 out) /\
   (let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v h0 bscalar) in
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_four_fw S.mk_ed25519_comm_monoid
      g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4))

let point_mul_g_noalloc out bscalar q1 q2 q3 q4 =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
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

  let r1 = sub bscalar 0ul 1ul in
  let r2 = sub bscalar 1ul 1ul in
  let r3 = sub bscalar 2ul 1ul in
  let r4 = sub bscalar 3ul 1ul in
  SPT256.lemma_decompose_nat256_as_four_u64_lbignum (as_seq h0 bscalar);

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


inline_for_extraction noextract
val point_mul_g_mk_q1234: out:point -> bscalar:lbuffer uint64 4ul -> q1:point ->
  Stack unit
  (requires fun h ->
    live h bscalar /\ live h out /\ live h q1 /\
    disjoint out bscalar /\ disjoint out q1 /\
    BD.bn_v h bscalar < pow2 256 /\
    F51.linv (as_seq h q1) /\ refl (as_seq h q1) == g_aff)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.linv (as_seq h1 out) /\
   (let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 (BD.bn_v h0 bscalar) in
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_four_fw S.mk_ed25519_comm_monoid
      g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4))

let point_mul_g_mk_q1234 out bscalar q1 =
  push_frame ();
  let q2 = mk_ext_g_pow2_64 () in
  let q3 = mk_ext_g_pow2_128 () in
  let q4 = mk_ext_g_pow2_192 () in
  ext_g_pow2_64_lseq_lemma ();
  ext_g_pow2_128_lseq_lemma ();
  ext_g_pow2_192_lseq_lemma ();
  point_mul_g_noalloc out bscalar q1 q2 q3 q4;
  pop_frame ()


val lemma_exp_four_fw_local: b:BSeq.lbytes 32 ->
  Lemma (let bn = BSeq.nat_from_bytes_le b in
    let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 bn in
    let cm = S.mk_ed25519_comm_monoid in
    LE.exp_four_fw cm g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 ==
    S.to_aff_point (S.point_mul_g b))

let lemma_exp_four_fw_local b =
  let bn = BSeq.nat_from_bytes_le b in
  let (b0, b1, b2, b3) = SPT256.decompose_nat256_as_four_u64 bn in
  let cm = S.mk_ed25519_comm_monoid in
  let res = LE.exp_four_fw cm g_aff 64 b0 g_pow2_64 b1 g_pow2_128 b2 g_pow2_192 b3 4 in
  assert (res == SPT256.exp_as_exp_four_nat256_precomp cm g_aff bn);
  SPT256.lemma_point_mul_base_precomp4 cm g_aff bn;
  assert (res == LE.pow cm g_aff bn);
  SE.exp_fw_lemma S.mk_ed25519_concrete_ops g_c 256 bn 4;
  LE.exp_fw_lemma cm g_aff 256 bn 4;
  assert (S.to_aff_point (S.point_mul_g b) == LE.pow cm g_aff bn)


[@CInline]
let point_mul_g out scalar =
  push_frame ();
  let h0 = ST.get () in
  let bscalar = create 4ul (u64 0) in
  convert_scalar scalar bscalar;
  let q1 = create 20ul (u64 0) in
  make_g q1;
  point_mul_g_mk_q1234 out bscalar q1;
  lemma_exp_four_fw_local (as_seq h0 scalar);
  pop_frame ()


inline_for_extraction noextract
val point_mul_g_double_vartime_noalloc:
    out:point
  -> scalar1:lbuffer uint64 4ul -> q1:point
  -> scalar2:lbuffer uint64 4ul -> q2:point
  -> table2: lbuffer uint64 640ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\ live h table2 /\

    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out table2 /\

    BD.bn_v h scalar1 < pow2 256 /\ BD.bn_v h scalar2 < pow2 256 /\
    F51.linv (as_seq h q1) /\ F51.linv (as_seq h q2) /\
    F51.point_eval h q1 == g_c /\
    table_inv_w5 (as_seq h q2) (as_seq h table2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.linv (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h0 scalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h0 scalar2) 5)

let point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2 =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
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
    (to_const precomp_basepoint_table_w5) (to_const table2) out


inline_for_extraction noextract
val point_mul_g_double_vartime_table:
    out:point
  -> scalar1:lbuffer uint64 4ul -> q1:point
  -> scalar2:lbuffer uint64 4ul -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\

    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\

    BD.bn_v h scalar1 < pow2 256 /\ BD.bn_v h scalar2 < pow2 256 /\
    F51.linv (as_seq h q1) /\ F51.linv (as_seq h q2) /\
    F51.point_eval h q1 == g_c)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.linv (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h0 scalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h0 scalar2) 5)

let point_mul_g_double_vartime_table out scalar1 q1 scalar2 q2 =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 5 == v table_len);

  push_frame ();
  let table2 = create (table_len *! len) (u64 0) in
  PT.lprecomp_table len ctx_len k (null uint64) q2 table_len table2;

  point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2;
  pop_frame ()


inline_for_extraction noextract
val point_mul_g_double_vartime_aux:
    out:point
  -> scalar1:lbuffer uint8 32ul -> q1:point
  -> scalar2:lbuffer uint8 32ul -> q2:point
  -> bscalar1:lbuffer uint64 4ul
  -> bscalar2:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\ live h bscalar1 /\ live h bscalar2 /\

    disjoint scalar1 bscalar1 /\ disjoint scalar2 bscalar2 /\ disjoint scalar2 bscalar1 /\
    disjoint scalar1 bscalar2 /\ disjoint bscalar1 bscalar2 /\ disjoint bscalar1 out /\
    disjoint bscalar1 q1 /\ disjoint bscalar1 q2 /\ disjoint bscalar2 out /\
    disjoint bscalar2 q1 /\ disjoint bscalar2 q2 /\ eq_or_disjoint q1 q2 /\
    disjoint q1 out /\ disjoint q2 out /\ disjoint scalar1 out /\ disjoint scalar2 out /\

    F51.linv (as_seq h q1) /\ F51.linv (as_seq h q2) /\
    F51.point_eval h q1 == g_c)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc bscalar1 |+| loc bscalar2) h0 h1 /\
    F51.linv (as_seq h1 out) /\
    BD.bn_v h1 bscalar1 == BSeq.nat_from_bytes_le (as_seq h0 scalar1) /\
    BD.bn_v h1 bscalar2 == BSeq.nat_from_bytes_le (as_seq h0 scalar2) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h1 bscalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h1 bscalar2) 5)

let point_mul_g_double_vartime_aux out scalar1 q1 scalar2 q2 bscalar1 bscalar2 =
  let h0 = ST.get () in
  convert_scalar scalar1 bscalar1;
  convert_scalar scalar2 bscalar2;
  let h1 = ST.get () in
  assert (BD.bn_v h1 bscalar1 == BSeq.nat_from_bytes_le (as_seq h0 scalar1));
  assert (BD.bn_v h1 bscalar2 == BSeq.nat_from_bytes_le (as_seq h0 scalar2));
  point_mul_g_double_vartime_table out bscalar1 q1 bscalar2 q2


val point_mul_g_double_vartime:
    out:point
  -> scalar1:lbuffer uint8 32ul
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\
    live h scalar2 /\ live h q2 /\
    disjoint q2 out /\ disjoint scalar1 out /\ disjoint scalar2 out /\
    F51.linv (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.linv (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point g_c) 256 (BSeq.nat_from_bytes_le (as_seq h0 scalar1))
      (S.to_aff_point (F51.point_eval h0 q2)) (BSeq.nat_from_bytes_le (as_seq h0 scalar2)) 5)

[@CInline]
let point_mul_g_double_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let tmp = create 28ul (u64 0) in
  let g = sub tmp 0ul 20ul in
  let bscalar1 = sub tmp 20ul 4ul in
  let bscalar2 = sub tmp 24ul 4ul in
  make_g g;
  point_mul_g_double_vartime_aux out scalar1 g scalar2 q2 bscalar1 bscalar2;
  pop_frame ()


[@CInline]
let point_negate_mul_double_g_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let q2_neg = create 20ul (u64 0) in
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_negate (F51.refl_ext_point (as_seq h0 q2));
  Hacl.Impl.Ed25519.PointNegate.point_negate q2 q2_neg;
  let h1 = ST.get () in
  point_mul_g_double_vartime out scalar1 scalar2 q2_neg;
  SE.exp_double_fw_lemma S.mk_ed25519_concrete_ops
    g_c 256 (BSeq.nat_from_bytes_le (as_seq h1 scalar1))
    (F51.point_eval h1 q2_neg) (BSeq.nat_from_bytes_le (as_seq h1 scalar2)) 5;
  pop_frame ()
