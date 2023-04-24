module Hacl.Impl.P256.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery

friend Hacl.Bignum256

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create one

[@CInline]
let make_qone f =
  [@inline_let] let f0 = u64 0xc46353d039cdaaf in
  [@inline_let] let f1 = u64 0x4319055258e8617b in
  [@inline_let] let f2 = u64 0x0 in
  [@inline_let] let f3 = u64 0xffffffff in
  assert_norm (v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192 < S.order);
  assert_norm (v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192 == SM.to_qmont 1);
  SM.lemma_to_from_qmont_id 1;
  bn_make_u64_4 f f0 f1 f2 f3


///  Comparison

[@CInline]
let bn_is_lt_order_mask4 f =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem () in
  make_order tmp;
  let c = bn_sub4 tmp f tmp in
  assert (if v c = 0 then as_nat h0 f >= S.order else as_nat h0 f < S.order);
  pop_frame ();
  u64 0 -. c


[@CInline]
let bn_is_lt_order_and_gt_zero_mask4 f =
  let h0 = ST.get () in
  let is_lt_order = bn_is_lt_order_mask4 f in
  assert (v is_lt_order = (if as_nat h0 f < S.order then ones_v U64 else 0));
  let is_eq_zero = bn_is_zero_mask4 f in
  assert (v is_eq_zero = (if as_nat h0 f = 0 then ones_v U64 else 0));
  lognot_lemma is_eq_zero;
  assert (v (lognot is_eq_zero) = (if 0 < as_nat h0 f then ones_v U64 else 0));

  let res = logand is_lt_order (lognot is_eq_zero) in
  logand_lemma is_lt_order (lognot is_eq_zero);
  assert (v res == (if 0 < as_nat h0 f && as_nat h0 f < S.order then ones_v U64 else 0));
  res


let load_qelem_conditional res b =
  push_frame ();
  bn_from_bytes_be4 res b;
  let is_b_valid = bn_is_lt_order_and_gt_zero_mask4 res in

  let oneq = create_felem () in
  bn_set_one4 oneq;
  let h0 = ST.get () in
  Lib.ByteBuffer.buf_mask_select res oneq is_b_valid res;
  let h1 = ST.get () in
  assert (as_seq h1 res == (if (v is_b_valid = 0) then as_seq h0 oneq else as_seq h0 res));
  pop_frame ();
  is_b_valid


///  Field Arithmetic

val qmod_short_lemma: a:nat{a < pow2 256} ->
  Lemma (let r = if a >= S.order then a - S.order else a in r = a % S.order)

let qmod_short_lemma a =
  let r = if a >= S.order then a - S.order else a in
  if a >= S.order then begin
    Math.Lemmas.lemma_mod_sub a S.order 1;
    assert_norm (pow2 256 - S.order < S.order);
    Math.Lemmas.small_mod r S.order end
  else
   Math.Lemmas.small_mod r S.order


[@CInline]
let qmod_short res x =
  push_frame ();
  let tmp = create_felem () in
  make_order tmp;
  let h0 = ST.get () in
  let c = bn_sub4 tmp x tmp in
  bn_cmovznz4 res c tmp x;
  BD.bn_eval_bound (as_seq h0 x) 4;
  qmod_short_lemma (as_nat h0 x);
  pop_frame ()


[@CInline]
let qadd res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem () in
  make_order n;
  bn_add_mod4 res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.order);
  SM.qmont_add_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


val qmont_reduction: res:felem -> x:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.order * S.order)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.qmont_R_inv % S.order)

[@CInline]
let qmont_reduction res x =
  push_frame ();
  let n = create_felem () in
  make_order n;

  let h0 = ST.get () in
  BM.bn_mont_reduction Hacl.Bignum256.bn_inst n (u64 0xccd1c8aaee00bc4f) x res;
  SM.bn_qmont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()


[@CInline]
let from_qmont res x =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  update_sub tmp 0ul 4ul x;
  BD.bn_eval_update_sub 4 (as_seq h0 x) 8;
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp = as_nat h0 x);
  assert_norm (S.order < S.order * S.order);
  qmont_reduction res tmp;
  pop_frame ()


[@CInline]
let qmul res x y =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_mul4 tmp x y;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 y) S.order;
  qmont_reduction res tmp;
  SM.qmont_mul_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


[@CInline]
let qsqr res x =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_sqr4 tmp x;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 x) S.order;
  qmont_reduction res tmp;
  SM.qmont_mul_lemma (as_nat h0 x) (as_nat h0 x);
  pop_frame ()
