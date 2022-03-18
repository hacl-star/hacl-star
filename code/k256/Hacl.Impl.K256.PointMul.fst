module Hacl.Impl.K256.PointMul

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation

module S = Spec.K256

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///////////////////////////////////////////

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl (p:LSeq.lseq uint64 15{point_inv_lseq p}) : GTot S.proj_point =
  point_eval_lseq p

inline_for_extraction noextract
let mk_to_k256_concrete_ops : BE.to_concrete_ops U64 15ul 0ul = {
  BE.t_spec = S.proj_point;
  BE.concr_ops = S.mk_k256_concrete_ops;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_lseq;
  BE.refl = refl;
  }


inline_for_extraction noextract
val point_add : BE.lmul_st U64 15ul 0ul mk_to_k256_concrete_ops
let point_add ctx x y xy =
  Hacl.Impl.K256.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 15ul 0ul mk_to_k256_concrete_ops
let point_double ctx x xx =
  Hacl.Impl.K256.PointDouble.point_double xx x


inline_for_extraction noextract
let mk_k256_concrete_ops : BE.concrete_ops U64 15ul 0ul = {
  BE.to = mk_to_k256_concrete_ops;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}

//////////////////////////////////////////////////////

inline_for_extraction noextract
val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ point_eval h1 p == S.point_at_inf)

let make_point_at_inf p =
  let px, py, pz = getx p, gety p, getz p in
  set_zero px;
  set_one py;
  set_zero pz


inline_for_extraction noextract
val make_g: g:point -> Stack unit
  (requires fun h -> live h g)
  (ensures  fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    point_inv h1 g /\
    point_eval h1 g == S.g)

let make_g g =
  let gx, gy, gz = getx g, gety g, getz g in

  [@inline_let]
  let x =
   (u64 0x2815b16f81798,
    u64 0xdb2dce28d959f,
    u64 0xe870b07029bfc,
    u64 0xbbac55a06295c,
    u64 0x79be667ef9dc) in

  assert_norm (0x79be667ef9dc < max48);
  assert_norm (0xe1108a8fd17b4 < max52);
  assert_norm (S.g_x == as_nat5 x);
  make_u52_5 gx x;

  [@inline_let]
  let y =
   (u64 0x7d08ffb10d4b8,
    u64 0x48a68554199c4,
    u64 0xe1108a8fd17b4,
    u64 0xc4655da4fbfc0,
    u64 0x483ada7726a3) in

  assert_norm (S.g_y == as_nat5 y);
  make_u52_5 gy y;

  set_one gz


// TODO: fix extraction for bn_from_bytes_le/be
val point_mul: out:point -> scalar:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ live h q /\
    disjoint out q /\ disjoint out scalar /\ disjoint q scalar /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul (qas_nat h0 scalar) (point_eval h0 q))

let point_mul out scalar q =
  make_point_at_inf out;
  BE.lexp_fw_consttime 15ul 0ul mk_k256_concrete_ops (null uint64) q 4ul 256ul scalar out 4ul


val point_mul_double_vartime:
  out:point -> scalar1:qelem -> q1:point -> scalar2:qelem -> q2:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\ live h scalar2 /\ live h q2 /\
    disjoint q1 out /\ disjoint q2 out /\ disjoint q1 q2 /\
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
let point_mul_double_vartime out scalar1 q1 scalar2 q2 =
  make_point_at_inf out;
  ME.lexp_double_fw_vartime 15ul 0ul mk_k256_concrete_ops (null uint64) q1 4ul 256ul scalar1 q2 scalar2 out 4ul


val point_mul_g: out:point -> scalar:qelem -> Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ disjoint out scalar /\
    qas_nat h scalar < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.point_mul_g (qas_nat h0 scalar))

[@CInline]
let point_mul_g out scalar =
  push_frame ();
  let g = create 15ul (u64 0) in
  make_g g;
  point_mul out scalar g;
  pop_frame ()


val point_mul_g_double_vartime: out:point -> scalar1:qelem -> scalar2:qelem -> q2:point ->
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
let point_mul_g_double_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let g = create 15ul (u64 0) in
  make_g g;
  point_mul_double_vartime out scalar1 g scalar2 q2;
  pop_frame ()
