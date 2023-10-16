module Hacl.Impl.PCurves.Qinv.P384

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
module SI256 = Hacl.Spec.PCurves.Qinv.P384
module QI = Hacl.Impl.PCurves.Qinv
module SM = Hacl.Spec.PCurves.Montgomery

open Spec.P384
open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Bignum.P384
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Constants.P384
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Field.P384
open Hacl.Impl.PCurves.Scalar
open Hacl.Impl.PCurves.Scalar.P384
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Qinv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val qexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == M.pow_mod #S.order (as_nat h0 a) (as_nat h0 b))

[@CInline]
let qexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm(pow2 5 == 32);
  bn_v_is_as_nat6 (as_seq h0 b);
  assume(as_nat h0 b < pow2 384);
  BE.lexp_fw_vartime 6ul 0ul
    mk_pcurve_order_concrete_ops 5ul (null uint64) a 6ul 384ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (as_nat h0 a) 384 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (as_nat h0 a) 384 (as_nat h0 b) 5;
  admit();
  assert (as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.order (as_nat h0 a) (as_nat h0 b);
  assert (as_nat h1 out == M.pow (as_nat h0 a) (as_nat h0 b) % S.order);
  M.lemma_pow_mod #S.order (as_nat h0 a) (as_nat h0 b)


inline_for_extraction noextract
val make_order384_minus_2: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == S.order - 2)

let make_order384_minus_2 n =
    // 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971
    [@inline_let] let n0 = u64 0xecec196accc52971 in
    [@inline_let] let n1 = u64 0x581a0db248b0a77a in
    [@inline_let] let n2 = u64 0xc7634d81f4372ddf in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n3 * pow2 256 + v n3 * pow2 320 = Spec.P384.p384_order - 2);
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_qinv: res:felem -> a:felem -> Stack unit
   (requires fun h ->
     live h a /\ live h res /\ eq_or_disjoint a res /\
     as_nat h a < S.order)
   (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
     as_nat h1 res < S.order /\
     qmont_as_nat h1 res == S.qinv (qmont_as_nat h0 a))

[@CInline]
let p384_qinv res a =
  push_frame ();
  let b = create 6ul (u64 0) in
  make_order384_minus_2 b;
  qexp_vartime res a b;
  admit();
  pop_frame ()

inline_for_extraction
instance p384_inv_sqrt : curve_inv_sqrt = {
  finv = Hacl.Impl.PCurves.Finv.P384.p384_finv;
  qinv = p384_qinv;
  fsqrt = Hacl.Impl.PCurves.Finv.P384.p384_fsqrt
}
