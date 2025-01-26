module Hacl.Impl.PCurves.PointMul

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Point

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable
module BD = Hacl.Spec.Bignum.Definitions

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

module PP = Hacl.Impl.PCurves.PrecompTable

#set-options "--z3rlimit 90 --fuel 0 --ifuel 0"

let point_mul_gen {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} {| point_ops |} res scalar p =
  let h0 = ST.get () in
  SE.exp_fw_lemma S.mk_pcurve_concrete_ops
    (from_mont_point (as_point_nat h0 p)) cp.bits (as_nat h0 scalar) 4;
  assert (v (3ul *! cp.bn_limbs) == 3 * v cp.bn_limbs);
  BE.lexp_fw_consttime (3ul *! cp.bn_limbs) 0ul mk_pcurve_concrete_ops 4ul (null uint64) p cp.bn_limbs (size cp.bits) scalar res


