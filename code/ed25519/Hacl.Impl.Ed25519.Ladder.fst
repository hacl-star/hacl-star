module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable
module SPT = Hacl.Spec.PrecompBaseTable

module BD = Hacl.Bignum.Definitions
module BC = Hacl.Bignum.Convert
module SC = Hacl.Spec.Bignum.Convert

module S = Spec.Ed25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

////////////////////////////////////////////////////

unfold
let a_spec = S.aff_point_c

unfold
let refl (a:LSeq.lseq uint64 20{F51.linv a}) : GTot a_spec =
  S.to_aff_point (F51.refl_ext_point a)

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

inline_for_extraction noextract
let mk_to_ed25519_comm_monoid : BE.to_comm_monoid U64 20ul 0ul = {
  BE.a_spec = a_spec;
  BE.comm_monoid = S.mk_ed25519_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = F51.linv;
  BE.refl = refl;
  }


inline_for_extraction noextract
val point_add : BE.lmul_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_add_lemma
    (F51.refl_ext_point (as_seq h0 x)) (F51.refl_ext_point (as_seq h0 y));
  Hacl.Impl.Ed25519.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_double_lemma (F51.refl_ext_point (as_seq h0 x));
  Hacl.Impl.Ed25519.PointDouble.point_double xx x


val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.point_inv_t h1 b /\ F51.inv_ext_point (as_seq h1 b) /\
    S.to_aff_point (F51.point_eval h1 b) == S.aff_point_at_infinity)

let make_point_inf b =
  let x = getx b in
  let y = gety b in
  let z = getz b in
  let t = gett b in
  make_zero x;
  make_one y;
  make_one z;
  make_zero t;
  let h1 = ST.get () in
  assert (F51.point_eval h1 b == S.point_at_infinity);
  Spec.Ed25519.Lemmas.to_aff_point_at_infinity_lemma ()


inline_for_extraction noextract
val point_zero : BE.lone_st U64 20ul 0ul mk_to_ed25519_comm_monoid
let point_zero ctx one = make_point_inf one


inline_for_extraction noextract
let mk_ed25519_concrete_ops : BE.concrete_ops U64 20ul 0ul = {
  BE.to = mk_to_ed25519_comm_monoid;
  BE.lone = point_zero;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}

//////////////////////////////////////////////

inline_for_extraction noextract
val ext_point_to_list: p:S.ext_point_c
  -> x:list uint64{FStar.List.Tot.length x = 20 /\
    mk_to_ed25519_comm_monoid.BE.linv (Seq.seq_of_list x)}

let ext_point_to_list p =
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list_lemma p;
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list p


val lemma_refl: x:S.ext_point_c ->
  Lemma (S.mk_ed25519_concrete_ops.SE.to.SE.refl x ==
    mk_to_ed25519_comm_monoid.BE.refl (Seq.seq_of_list (ext_point_to_list x)))

let lemma_refl x =
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list_eval x


inline_for_extraction noextract
let mk_ed25519_precomp_base_table: SPT.mk_precomp_base_table S.ext_point_c U64 20ul 0ul = {
  SPT.concr_ops = S.mk_ed25519_concrete_ops;
  SPT.to_cm = mk_to_ed25519_comm_monoid;
  SPT.to_list = ext_point_to_list;
  SPT.lemma_refl = lemma_refl;
}

inline_for_extraction noextract
let g_c : S.ext_point_c =
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  S.g

unfold let precomp_basepoint_table_list: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15)

inline_for_extraction noextract
let precomp_basepoint_table_lseq : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  Seq.seq_of_list precomp_basepoint_table_list


inline_for_extraction noextract
let pow_base_point (k:nat) =
  LE.pow S.mk_ed25519_comm_monoid (S.to_aff_point g_c) k

unfold
let precomp_table_acc_inv
  (table_len:nat{table_len * 20 <= max_size_t})
  (table:LSeq.lseq uint64 (table_len * 20))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right 20 j table_len;
  Math.Lemmas.lemma_mult_le_right 20 (j + 1) table_len;
  let bj = LSeq.sub table (j * 20) 20 in
  F51.linv bj /\ refl bj == pow_base_point j

val precomp_basepoint_table_lemma: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv 16 precomp_basepoint_table_lseq i)
let precomp_basepoint_table_lemma () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  SPT.precomp_base_table_lemma mk_ed25519_precomp_base_table g_c 16 precomp_basepoint_table_lseq

/////////////////////////////////////////////////////

inline_for_extraction noextract
val make_g: g:point -> Stack unit
  (requires fun h -> live h g)
  (ensures fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    F51.point_inv_t h1 g /\ F51.inv_ext_point (as_seq h1 g) /\
    F51.point_eval h1 g == S.g)

let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in

  [@inline_let] let (x0, x1, x2, x3, x4) =
    (u64 0x00062d608f25d51a,
     u64 0x000412a4b4f6592a,
     u64 0x00075b7171a4b31d,
     u64 0x0001ff60527118fe,
     u64 0x000216936d3cd6e5) in

  [@inline_let] let (y0, y1, y2, y3, y4) =
    (u64 0x0006666666666658,
     u64 0x0004cccccccccccc,
     u64 0x0001999999999999,
     u64 0x0003333333333333,
     u64 0x0006666666666666) in

  [@inline_let] let (t0, t1, t2, t3, t4) =
    (u64 0x00068ab3a5b7dda3,
     u64 0x00000eea2a5eadbb,
     u64 0x0002af8df483c27e,
     u64 0x000332b375274732,
     u64 0x00067875f0fd78b7) in

  make_u64_5 gx x0 x1 x2 x3 x4;
  make_u64_5 gy y0 y1 y2 y3 y4;
  make_one gz;
  make_u64_5 gt t0 t1 t2 t3 t4;

  (**) assert_norm (Spec.Ed25519.g_x ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (x0, x1, x2, x3, x4) % Spec.Curve25519.prime);
  (**) assert_norm (Spec.Ed25519.g_y ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (y0, y1, y2, y3, y4) % Spec.Curve25519.prime);
  (**) assert_norm (Mktuple4?._4 Spec.Ed25519.g ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (t0, t1, t2, t3, t4) % Spec.Curve25519.prime);
  let h1 = ST.get () in
  assert (F51.point_inv_t h1 g);
  assert (F51.point_eval h1 g == Spec.Ed25519.g);
  Spec.Ed25519.Lemmas.g_is_on_curve ()


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


val point_mul:
    out:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h q /\ live h out /\
    disjoint q out /\ disjoint q scalar /\
    F51.point_inv_t h q /\ F51.inv_ext_point (as_seq h q))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_mul (as_seq h0 scalar) (F51.point_eval h0 q)))

let point_mul out scalar q =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_ed25519_concrete_ops
    (F51.point_eval h0 q) 256 (BSeq.nat_from_bytes_le (as_seq h0 scalar)) 4;
  push_frame ();
  let bscalar = create 4ul (u64 0) in
  convert_scalar scalar bscalar;
  point_mul_noalloc out bscalar q;
  pop_frame ()

////////////////////////////////////////

inline_for_extraction noextract
let table_inv : BE.table_inv_t U64 20ul 16ul =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  BE.table_inv_precomp len ctx_len k l table_len


let precomp_basepoint_table:
  x:glbuffer uint64 320ul{witnessed x precomp_basepoint_table_lseq /\ recallable x} =
  createL_global precomp_basepoint_table_list


inline_for_extraction noextract
val point_mul_g_noalloc:
    out:point
  -> bscalar:lbuffer uint64 4ul
  -> g:point -> Stack unit
  (requires fun h ->
    live h out /\ live h g /\ live h bscalar /\
    disjoint out g /\ disjoint bscalar out /\ disjoint bscalar g /\
    F51.point_inv_t h g /\ F51.inv_ext_point (as_seq h g) /\
    F51.point_eval h g == g_c /\ BD.bn_v h bscalar < pow2 256)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_fw S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 g)) 256 (BD.bn_v h0 bscalar) 4)

let point_mul_g_noalloc out bscalar g =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 256ul in

  let h0 = ST.get () in
  recall_contents precomp_basepoint_table precomp_basepoint_table_lseq;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma ();
  assert (table_inv (as_seq h1 g) (as_seq h1 precomp_basepoint_table));
  assert (F51.point_eval h1 g == g_c);

  BE.mk_lexp_fw_table len ctx_len k l table_len
    table_inv
    (BE.lprecomp_get_consttime len ctx_len k l table_len)
    (null uint64) g bLen bBits bscalar (to_const precomp_basepoint_table) out


val point_mul_g:
    out:point
  -> scalar:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ disjoint out scalar)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_mul_g (as_seq h0 scalar)))

[@CInline]
let point_mul_g out scalar =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_ed25519_concrete_ops
    g_c 256 (BSeq.nat_from_bytes_le (as_seq h0 scalar)) 4;

  push_frame ();
  let g = create 20ul (u64 0) in
  make_g g;

  let bscalar = create 4ul (u64 0) in
  convert_scalar scalar bscalar;
  point_mul_g_noalloc out bscalar g;
  pop_frame ()


inline_for_extraction noextract
val point_mul_g_double_vartime_noalloc:
    out:point
  -> scalar1:lbuffer uint64 4ul -> q1:point
  -> scalar2:lbuffer uint64 4ul -> q2:point
  -> table2: lbuffer uint64 320ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\
    live h scalar2 /\ live h q2 /\ live h table2 /\

    eq_or_disjoint q1 q2 /\ disjoint out q1 /\ disjoint out q2 /\
    disjoint out scalar1 /\ disjoint out scalar2 /\ disjoint out table2 /\

    BD.bn_v h scalar1 < pow2 256 /\ BD.bn_v h scalar2 < pow2 256 /\
    F51.point_inv_t h q1 /\ F51.inv_ext_point (as_seq h q1) /\
    F51.point_eval h q1 == g_c /\
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2) /\
    table_inv (as_seq h q2) (as_seq h table2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h0 scalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h0 scalar2) 4)

let point_mul_g_double_vartime_noalloc out scalar1 q1 scalar2 q2 table2 =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  [@inline_let] let bLen = 4ul in
  [@inline_let] let bBits = 256ul in

  let h0 = ST.get () in
  recall_contents precomp_basepoint_table precomp_basepoint_table_lseq;
  let h1 = ST.get () in
  precomp_basepoint_table_lemma ();
  assert (table_inv (as_seq h1 q1) (as_seq h1 precomp_basepoint_table));
  assert (table_inv (as_seq h1 q2) (as_seq h1 table2));

  ME.mk_lexp_double_fw_tables len ctx_len k l table_len
    table_inv table_inv
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (BE.lprecomp_get_vartime len ctx_len k l table_len)
    (null uint64) q1 bLen bBits scalar1 q2 scalar2
    (to_const precomp_basepoint_table) (to_const table2) out


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
    F51.point_inv_t h q1 /\ F51.inv_ext_point (as_seq h q1) /\
    F51.point_eval h q1 == g_c /\
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h0 scalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h0 scalar2) 4)

let point_mul_g_double_vartime_table out scalar1 q1 scalar2 q2 =
  [@inline_let] let len = 20ul in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_ed25519_concrete_ops in
  [@inline_let] let table_len = 16ul in

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

    F51.point_inv_t h q1 /\ F51.inv_ext_point (as_seq h q1) /\
    F51.point_eval h q1 == g_c /\
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc bscalar1 |+| loc bscalar2) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    BD.bn_v h1 bscalar1 == BSeq.nat_from_bytes_le (as_seq h0 scalar1) /\
    BD.bn_v h1 bscalar2 == BSeq.nat_from_bytes_le (as_seq h0 scalar2) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point (F51.point_eval h0 q1)) 256 (BD.bn_v h1 bscalar1)
      (S.to_aff_point (F51.point_eval h0 q2)) (BD.bn_v h1 bscalar2) 4)

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
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    LE.exp_double_fw #S.aff_point_c S.mk_ed25519_comm_monoid
      (S.to_aff_point g_c) 256 (BSeq.nat_from_bytes_le (as_seq h0 scalar1))
      (S.to_aff_point (F51.point_eval h0 q2)) (BSeq.nat_from_bytes_le (as_seq h0 scalar2)) 4)

[@CInline]
let point_mul_g_double_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let g = create 20ul (u64 0) in
  make_g g;

  let bscalar1 = create 4ul (u64 0) in
  let bscalar2 = create 4ul (u64 0) in
  point_mul_g_double_vartime_aux out scalar1 g scalar2 q2 bscalar1 bscalar2;
  pop_frame ()


val point_negate_mul_double_g_vartime:
    out:point
  -> scalar1:lbuffer uint8 32ul
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\
    live h scalar2 /\ live h q2 /\
    disjoint q2 out /\ disjoint scalar1 out /\ disjoint scalar2 out /\
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_negate_mul_double_g
      (as_seq h0 scalar1) (as_seq h0 scalar2) (F51.point_eval h0 q2)))

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
    (F51.point_eval h1 q2_neg) (BSeq.nat_from_bytes_le (as_seq h1 scalar2)) 4;
  pop_frame ()
