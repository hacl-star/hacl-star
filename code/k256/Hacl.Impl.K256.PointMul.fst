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

module BD = Hacl.Bignum.Definitions
module SD = Hacl.Spec.Bignum.Definitions
module BC = Hacl.Bignum.Convert
module SC = Hacl.Spec.Bignum.Convert

module S = Spec.K256

open Hacl.K256.Field
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///////////////////////////////////////////

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl (p:LSeq.lseq uint64 12{point_inv_lseq p}) : GTot S.aff_point =
  S.to_aff_point (point_as_nat3_proj_lseq p)

inline_for_extraction noextract
let mk_to_k256_cm : BE.to_comm_monoid U64 12ul 0ul = {
  BE.a_spec = S.aff_point;
  BE.comm_monoid = S.mk_k256_cm;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_lseq;
  BE.refl = refl;
  }


inline_for_extraction noextract
val point_add : BE.lmul_st U64 12ul 0ul mk_to_k256_cm
let point_add ctx x y xy =
  let h0 = ST.get () in
  S.to_aff_point_add_lemma (point_as_nat3_proj h0 x) (point_as_nat3_proj h0 y);
  Hacl.Impl.K256.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double : BE.lsqr_st U64 12ul 0ul mk_to_k256_cm
let point_double ctx x xx =
  let h0 = ST.get () in
  S.to_aff_point_double_lemma (point_as_nat3_proj h0 x);
  Hacl.Impl.K256.PointDouble.point_double xx x


inline_for_extraction noextract
let mk_k256_concrete_ops : BE.concrete_ops U64 12ul 0ul = {
  BE.to = mk_to_k256_cm;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}

//////////////////////////////////////////////////////

inline_for_extraction noextract
val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\
    S.to_aff_point (point_as_nat3_proj h1 p) == S.aff_point_at_inf)

let make_point_at_inf p =
  let px, py, pz = getx p, gety p, getz p in
  set_zero px;
  set_one py;
  set_zero pz;
  S.to_aff_point_at_infinity_lemma ()


inline_for_extraction noextract
val make_g: g:point -> Stack unit
  (requires fun h -> live h g)
  (ensures  fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    point_inv h1 g /\
    point_as_nat3_proj h1 g == S.g)

let make_g g =
  let gx, gy, gz = getx g, gety g, getz g in
  make_u64_4 gx
    (u64 0x59f2815b16f81798)
    (u64 0x029bfcdb2dce28d9)
    (u64 0x55a06295ce870b07)
    (u64 0x79be667ef9dcbbac);

  assert_norm (S.g_x == as_nat4
    (u64 0x59f2815b16f81798,
     u64 0x029bfcdb2dce28d9,
     u64 0x55a06295ce870b07,
     u64 0x79be667ef9dcbbac));

  make_u64_4 gy
    (u64 0x9c47d08ffb10d4b8)
    (u64 0xfd17b448a6855419)
    (u64 0x5da4fbfc0e1108a8)
    (u64 0x483ada7726a3c465);

  assert_norm (S.g_y == as_nat4
    (u64 0x9c47d08ffb10d4b8,
     u64 0xfd17b448a6855419,
     u64 0x5da4fbfc0e1108a8,
     u64 0x483ada7726a3c465));

  set_one gz


// TODO: fix extraction for bn_from_bytes_le/be
val point_mul: out:point -> scalar:lbuffer uint8 32ul -> q:point -> Stack unit
  (requires fun h ->
    live h out /\ live h scalar /\ live h q /\
    disjoint out q /\ disjoint out scalar /\ disjoint q scalar /\
    point_inv h q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_as_nat3_proj h1 out) ==
    S.to_aff_point (S.point_mul (as_seq h0 scalar) (point_as_nat3_proj h0 q)))

[@CInline]
let point_mul out scalar q =
  let h0 = ST.get () in
  push_frame ();
  let bscalar = create 4ul (u64 0) in
  BC.bn_from_bytes_be 32ul scalar bscalar;
  SC.bn_from_bytes_be_lemma #U64 32 (as_seq h0 scalar);

  make_point_at_inf out;
  BE.lexp_fw_consttime 12ul 0ul mk_k256_concrete_ops (null uint64) q 4ul 256ul bscalar out 4ul;
  pop_frame ()


val point_mul_double_vartime:
    out:point
  -> scalar1:lbuffer uint8 32ul
  -> q1:point
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h q1 /\ live h scalar2 /\ live h q2 /\
    disjoint q1 out /\ disjoint q2 out /\ disjoint q1 q2 /\
    point_inv h q1 /\ point_inv h q2)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_as_nat3_proj h1 out) ==
    S.to_aff_point (S.point_mul_double
      (as_seq h0 scalar1) (point_as_nat3_proj h0 q1)
      (as_seq h0 scalar2) (point_as_nat3_proj h0 q2)))

[@CInline]
let point_mul_double_vartime out scalar1 q1 scalar2 q2 =
  let h0 = ST.get () in
  push_frame ();
  let bscalar1 = create 4ul (u64 0) in
  BC.bn_from_bytes_be 32ul scalar1 bscalar1;
  SC.bn_from_bytes_be_lemma #U64 32 (as_seq h0 scalar1);

  let bscalar2 = create 4ul (u64 0) in
  BC.bn_from_bytes_be 32ul scalar2 bscalar2;
  SC.bn_from_bytes_be_lemma #U64 32 (as_seq h0 scalar2);

  make_point_at_inf out;
  ME.lexp_double_fw_vartime 12ul 0ul mk_k256_concrete_ops (null uint64) q1 4ul 256ul bscalar1 q2 bscalar2 out 4ul;
  pop_frame ()


val point_mul_g: out:point -> scalar:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ disjoint out scalar)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_as_nat3_proj h1 out) ==
    S.to_aff_point (S.point_mul_g (as_seq h0 scalar)))

[@CInline]
let point_mul_g out scalar =
  push_frame ();
  let g = create 12ul (u64 0) in
  make_g g;
  point_mul out scalar g;
  pop_frame ()


val point_mul_g_double_vartime:
    out:point
  -> scalar1:lbuffer uint8 32ul
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\ live h scalar2 /\ live h q2 /\
    disjoint q2 out /\
    point_inv h q2)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    S.to_aff_point (point_as_nat3_proj h1 out) ==
    S.to_aff_point (S.point_mul_double_g
      (as_seq h0 scalar1) (as_seq h0 scalar2) (point_as_nat3_proj h0 q2)))

[@CInline]
let point_mul_g_double_vartime out scalar1 scalar2 q2 =
  push_frame ();
  let g = create 12ul (u64 0) in
  make_g g;
  point_mul_double_vartime out scalar1 g scalar2 q2;
  pop_frame ()
