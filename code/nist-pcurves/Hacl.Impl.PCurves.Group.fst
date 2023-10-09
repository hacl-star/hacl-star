module Hacl.Impl.PCurves.Group

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BE = Hacl.Impl.Exponentiation.Definitions

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl {| cp:S.curve_params |} (p:LSeq.lseq uint64 (3*v cp.bn_limbs){point_inv_seq p}) : GTot S.aff_point =
  S.to_aff_point (from_mont_point (as_point_nat_seq p))

inline_for_extraction noextract
let mk_to_pcurve_comm_monoid {| cp:S.curve_params |} : BE.to_comm_monoid U64 (3ul *. cp.bn_limbs) 0ul = {
  BE.a_spec = S.aff_point;
  BE.comm_monoid = S.mk_pcurve_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_seq;
  BE.refl = refl;
}


inline_for_extraction noextract
val point_add {| cp:S.curve_params |} {| curve_constants |} {| curve_inv_sqrt|}: BE.lmul_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid
let point_add ctx x y xy =
  let h0 = ST.get () in
  SL.to_aff_point_add_lemma
    (from_mont_point (as_point_nat h0 x)) (from_mont_point (as_point_nat h0 y));
  Hacl.Impl.PCurves.PointAdd.point_add xy x y


inline_for_extraction noextract
val point_double {| cp:S.curve_params |} {| curve_constants |} {| curve_inv_sqrt|}: BE.lsqr_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid
let point_double ctx x xx =
  let h0 = ST.get () in
  SL.to_aff_point_double_lemma (from_mont_point (as_point_nat h0 x));
  Hacl.Impl.PCurves.PointDouble.point_double xx x


inline_for_extraction noextract
val point_zero {| cp:S.curve_params |} {| curve_constants |} {| curve_inv_sqrt|}: BE.lone_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid
let point_zero {| cp:S.curve_params |} ctx one =
  let h0 = ST.get () in
  SL.to_aff_point_at_infinity_lemma #cp;
  make_point_at_inf one


inline_for_extraction noextract
let mk_pcurve_concrete_ops {| cp:S.curve_params |} {| curve_constants |} {| curve_inv_sqrt|}: BE.concrete_ops U64 (3ul *. cp.bn_limbs) 0ul = {
  BE.to = mk_to_pcurve_comm_monoid;
  BE.lone = point_zero;
  BE.lmul = point_add;
  BE.lsqr = point_double;
}
