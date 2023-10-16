module Hacl.Impl.PCurves.Qinv.P521

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence
module M = Lib.NatMod

module S = Spec.PCurves
module SI = Hacl.Spec.PCurves.Qinv
module QI = Hacl.Impl.PCurves.Qinv
module SM = Hacl.Spec.PCurves.Montgomery

open Spec.P521
open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Bignum.P521
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Constants.P521
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Field.P521
open Hacl.Impl.PCurves.Scalar
open Hacl.Impl.PCurves.Scalar.P521
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Qinv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val qexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == M.pow_mod #S.order (as_nat h0 a) (as_nat h0 b))

inline_for_extraction noextract
let qexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm(pow2 5 == 32);
  bn_v_is_as_nat9 (as_seq h0 b);
  assume(as_nat h0 b < pow2 521);
  BE.lexp_fw_vartime 9ul 0ul
    mk_pcurve_order_concrete_ops 5ul (null uint64) a 9ul 521ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (as_nat h0 a) 521 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (as_nat h0 a) 521 (as_nat h0 b) 5;
  admit();
  assert (as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.order (as_nat h0 a) (as_nat h0 b);
  assert (as_nat h1 out == M.pow (as_nat h0 a) (as_nat h0 b) % S.order);
  M.lemma_pow_mod #S.order (as_nat h0 a) (as_nat h0 b)


inline_for_extraction noextract
val make_order521_minus_2: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == S.order - 2)

let make_order521_minus_2 n =
    // 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386407
    [@inline_let] let n0 = u64 0xbb6fb71e91386407 in 
    [@inline_let] let n1 = u64 0x3bb5c9b8899c47ae in
    [@inline_let] let n2 = u64 0x7fcc0148f709a5d0 in
    [@inline_let] let n3 = u64 0x51868783bf2f966b in
    [@inline_let] let n4 = u64 0xfffffffffffffffa in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    [@inline_let] let n6 = u64 0xffffffffffffffff in
    [@inline_let] let n7 = u64 0xffffffffffffffff in
    [@inline_let] let n8 = u64 0x1ff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 +
                 v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512
                 = Spec.P521.p521_order-2);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_qinv: res:felem -> a:felem -> Stack unit
   (requires fun h ->
     live h a /\ live h res /\ eq_or_disjoint a res /\
     as_nat h a < S.order)
   (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
     as_nat h1 res < S.order /\
     qmont_as_nat h1 res == S.qinv (qmont_as_nat h0 a))

[@CInline]
let p521_qinv res a =
  push_frame ();
  let b = create 9ul (u64 0) in
  make_order521_minus_2 b;
  let tmp = create 9ul (u64 0) in
  copy tmp a;
  qexp_vartime res tmp b;
  admit();
  pop_frame ()

inline_for_extraction
instance p521_inv_sqrt : curve_inv_sqrt = {
  finv = Hacl.Impl.PCurves.Finv.P521.p521_finv;
  qinv = p521_qinv;
  fsqrt = Hacl.Impl.PCurves.Finv.P521.p521_fsqrt
}
