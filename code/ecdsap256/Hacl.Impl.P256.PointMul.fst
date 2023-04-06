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
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble

//module LSeq = Lib.Sequence
//module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
//module ME = Hacl.Impl.MultiExponentiation
//module PT = Hacl.Impl.PrecompTable
//module SPT256 = Hacl.Spec.PrecompBaseTable256
//module BD = Hacl.Spec.Bignum.Definitions

module S = Spec.P256
module SL = Spec.P256.Lemmas
//module SM = Hacl.Spec.P256.Montgomery

include Hacl.Impl.P256.Group
//include Hacl.P256.PrecompTable

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
  Hacl.Spec.P256.Bignum.bn_v_is_as_nat (as_seq h0 scalar);
  SE.exp_fw_lemma S.mk_p256_concrete_ops
    (from_mont_point (as_point_nat h0 p)) 256 (as_nat h0 scalar) 4;
  BE.lexp_fw_consttime 12ul 0ul mk_p256_concrete_ops 4ul (null uint64) p 4ul 256ul scalar res


[@CInline]
let point_mul_g res scalar =
  push_frame ();
  let g = create_point () in
  make_base_point g;
  point_mul res scalar g;
  pop_frame ()


[@CInline]
let point_mul_double_g res scalar1 scalar2 p =
  push_frame ();
  let sg1 = create_point () in
  let sp2 = create_point () in
  let h0 = ST.get () in
  point_mul_g sg1 scalar1; // sg1 = [scalar1]G
  point_mul sp2 scalar2 p; // sp2 = [scalar2]P
  let h1 = ST.get () in
  assert (S.to_aff_point (from_mont_point (as_point_nat h1 sg1)) ==
    S.to_aff_point (S.point_mul_g (as_nat h0 scalar1)));
  assert (S.to_aff_point (from_mont_point (as_point_nat h1 sp2)) ==
    S.to_aff_point (S.point_mul (as_nat h0 scalar2) (from_mont_point (as_point_nat h0 p))));

  Hacl.Impl.P256.PointAdd.point_add res sg1 sp2;
  let h2 = ST.get () in
  SL.to_aff_point_add_lemma
    (from_mont_point (as_point_nat h1 sg1)) (from_mont_point (as_point_nat h1 sp2));
  SL.to_aff_point_add_lemma
    (S.point_mul_g (as_nat h0 scalar1))
    (S.point_mul (as_nat h0 scalar2) (from_mont_point (as_point_nat h0 p)));
  pop_frame ()
