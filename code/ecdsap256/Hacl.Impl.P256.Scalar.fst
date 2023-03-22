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
module SB = Hacl.Spec.P256.Bignum
module SM = Hacl.Spec.P256.Montgomery

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery

friend Hacl.Bignum256

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create one

[@CInline]
let make_qone n =
  [@inline_let] let n0 = u64 0xc46353d039cdaaf in
  [@inline_let] let n1 = u64 0x4319055258e8617b in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xffffffff in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ 1);
  assert_norm (SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == 1);
  bn_make_u64_4 n n0 n1 n2 n3


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
let qmod_short x res =
  push_frame ();
  let tmp = create_felem () in
  make_order tmp;
  let h0 = ST.get () in
  let c = bn_sub4 tmp x tmp in
  bn_cmovznz4 res c tmp x;
  SB.as_nat_bound (as_seq h0 x);
  qmod_short_lemma (as_nat h0 x);
  pop_frame ()


[@CInline]
let qadd x y res =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem () in
  make_order n;
  bn_add_mod4 res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.order);
  SM.qadd_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


val qmont_reduction: x:widefelem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.order * S.order)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.qmont_R_inv % S.order)

[@CInline]
let qmont_reduction x res =
  push_frame ();
  let n = create_felem () in
  make_order n;

  let h0 = ST.get () in
  BM.bn_mont_reduction Hacl.Bignum256.bn_inst n (u64 0xccd1c8aaee00bc4f) x res;
  let h1 = ST.get () in
  SB.bn_v_is_as_nat (as_seq h0 n);
  SB.bn_v_is_wide_as_nat (as_seq h0 x);
  assert (BD.bn_v (as_seq h0 n) == as_nat h0 n);
  assert (BD.bn_v (as_seq h0 x) == wide_as_nat h0 x);
  SM.qmont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  assert (BD.bn_v (as_seq h1 res) == BD.bn_v (as_seq h0 x) * SM.qmont_R_inv % S.order);
  SB.bn_v_is_as_nat (as_seq h1 res);
  assert (as_nat h1 res == wide_as_nat h0 x * SM.qmont_R_inv % S.order);
  pop_frame ()


[@CInline]
let from_qmont a res =
  push_frame ();
  let t = create_widefelem () in
  let t_low = sub t (size 0) (size 4) in
  let t_high = sub t (size 4) (size 4) in

  let h0 = ST.get () in
  copy t_low a;
  let h1 = ST.get () in
  assert (wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
  assert_norm (S.order < S.order * S.order);
  qmont_reduction t res;
  pop_frame ()


[@CInline]
let qmul a b res =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_mul4 tmp a b;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 a) (as_nat h0 b) S.order;
  qmont_reduction tmp res;
  SM.qmul_lemma (as_nat h0 a) (as_nat h0 b);
  pop_frame ()


[@CInline]
let qsqr a res =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_sqr4 tmp a;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 a) (as_nat h0 a) S.order;
  qmont_reduction tmp res;
  SM.qmul_lemma (as_nat h0 a) (as_nat h0 a);
  pop_frame ()
