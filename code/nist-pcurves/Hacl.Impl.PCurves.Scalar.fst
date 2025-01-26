module Hacl.Impl.PCurves.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Comparison


let bn_is_lt_order_mask_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} f =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem #cp in
  cc.make_order tmp;
  let c = bn_sub tmp f tmp in
  assert (if v c = 0 then as_nat h0 f >= S.order else as_nat h0 f < S.order);
  pop_frame ();
  u64 0 -. c



let bn_is_lt_order_and_gt_zero_mask {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} f =
  let h0 = ST.get () in
  let is_lt_order = bn_is_lt_order_mask_g f in
  assert (v is_lt_order = (if as_nat h0 f < S.order then ones_v U64 else 0));
  let is_eq_zero = bn_is_zero_mask f in
  assert (v is_eq_zero = (if as_nat h0 f = 0 then ones_v U64 else 0));
  lognot_lemma is_eq_zero;
  assert (v (lognot is_eq_zero) = (if 0 < as_nat h0 f then ones_v U64 else 0));

  let res = logand is_lt_order (lognot is_eq_zero) in
  logand_lemma is_lt_order (lognot is_eq_zero);
  assert (v res == (if 0 < as_nat h0 f && as_nat h0 f < S.order then ones_v U64 else 0));
  res


let load_qelem_conditional_g {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} res b =
  push_frame ();
  bn_from_bytes_be res b;
  let is_b_valid = bn_is_lt_order_and_gt_zero_mask res in

  let oneq = create_felem #cp in
  bn_set_one oneq;
  let h0 = ST.get () in
  Lib.ByteBuffer.buf_mask_select res oneq is_b_valid res;
  let h1 = ST.get () in
  assert (as_seq h1 res == (if (v is_b_valid = 0) then as_seq h0 oneq else as_seq h0 res));
  pop_frame ();
  is_b_valid


///  Field Arithmetic

val qmod_short_lemma {| cp:S.curve_params |} {| bn_ops |} {| CC.curve_constants |}:
  a:nat{a < 2 * cp.order} ->
  Lemma (let r = if a >= S.order then a - S.order else a in r = a % S.order)

let qmod_short_lemma {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} a = ()


let qmod_short_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x =
  push_frame ();
  let tmp = create_felem #cp in
  cc.make_order tmp;
  let h0 = ST.get () in
  let c = bn_sub tmp x tmp in
  bn_cmovznz res c tmp x;
  BD.bn_eval_bound (as_seq h0 x) (v cp.bn_limbs);
  qmod_short_lemma (as_nat h0 x);
  pop_frame ()



let qadd_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem #cp in
  cc.make_order n;
  bn_add_mod res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.order);
  SM.qmont_add_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


let from_qmont_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  update_sub tmp 0ul cp.bn_limbs x;
  BD.bn_eval_update_sub (v cp.bn_limbs) (as_seq h0 x) (2 * v cp.bn_limbs);
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp = as_nat h0 x);
  assert_norm (S.order < S.order * S.order);
  cc.qmont_reduction res tmp;
  pop_frame ()



let qmul_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x y =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_mul tmp x y;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 y) S.order;
  cc.qmont_reduction res tmp;
  SM.qmont_mul_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()



let qsqr_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_sqr tmp x;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 x) S.order;
  cc.qmont_reduction res tmp;
  SM.qmont_mul_lemma (as_nat h0 x) (as_nat h0 x);
  pop_frame ()
