module Hacl.Impl.PCurves.Qinv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Scalar

module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

module S = Spec.PCurves
module SI = Hacl.Spec.PCurves.Qinv
module SM = Hacl.Spec.PCurves.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv {| cp:S.curve_params |} (a:LSeq.lseq uint64 (v cp.bn_limbs)) : Type0 =
  BD.bn_v a < S.order

unfold
let refl  {| cp:S.curve_params |} (a:LSeq.lseq uint64 (v cp.bn_limbs){linv a}) : GTot S.qelem =
  SM.from_qmont (BD.bn_v a)


inline_for_extraction noextract
let mk_to_pcurve_order_comm_monoid  {| cp:S.curve_params |} : BE.to_comm_monoid U64 cp.bn_limbs 0ul = {
  BE.a_spec = S.qelem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}

inline_for_extraction noextract
val one_mod {| cp:S.curve_params |} {| curve_constants |} : BE.lone_st U64 cp.bn_limbs 0ul mk_to_pcurve_order_comm_monoid
let one_mod ctx one = make_qone one


inline_for_extraction noextract
val mul_mod  {| cp:S.curve_params |} {| curve_constants |} : BE.lmul_st U64 cp.bn_limbs 0ul mk_to_pcurve_order_comm_monoid
let mul_mod ctx x y xy = qmul xy x y


inline_for_extraction noextract
val sqr_mod  {| cp:S.curve_params |} {| curve_constants |} : BE.lsqr_st U64 cp.bn_limbs 0ul mk_to_pcurve_order_comm_monoid
let sqr_mod ctx x xx = qsqr xx x


inline_for_extraction noextract
let mk_pcurve_order_concrete_ops {| cp:S.curve_params |} {| curve_constants |} : BE.concrete_ops U64 cp.bn_limbs 0ul = {
  BE.to = mk_to_pcurve_order_comm_monoid;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


inline_for_extraction noextract
val qsquare_times_in_place {| cp:S.curve_params |} {| curve_constants |} (out:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ as_nat h out < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.order /\
    qmont_as_nat h1 out == SI.qsquare_times (qmont_as_nat h0 out) (v b))

let qsquare_times_in_place {| cp:S.curve_params |} {| curve_constants |} out b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 out) (v b);
  BE.lexp_pow2_in_place cp.bn_limbs 0ul mk_pcurve_order_concrete_ops (null uint64) out b


inline_for_extraction noextract
val qsquare_times {| cp:S.curve_params |} {| curve_constants |} (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.order /\
    qmont_as_nat h1 out == SI.qsquare_times (qmont_as_nat h0 a) (v b))

let qsquare_times {| cp:S.curve_params |} {| curve_constants |} out a b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 a) (v b);
  BE.lexp_pow2 cp.bn_limbs 0ul mk_pcurve_order_concrete_ops (null uint64) a b out


