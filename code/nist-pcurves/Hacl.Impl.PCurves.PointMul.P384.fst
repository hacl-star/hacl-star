module Hacl.Impl.PCurves.PointMul.P384

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

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

open Spec.P384
open Hacl.Impl.PCurves.Constants.P384
open Hacl.Impl.PCurves.Bignum.P384
open Hacl.Impl.PCurves.Field.P384
open Hacl.Impl.PCurves.Finv.P384
open Hacl.Impl.PCurves.Qinv.P384
open Hacl.Impl.PCurves.Group.P384
open Hacl.Impl.PCurves.PrecompTable.P384
open Hacl.Impl.PCurves.PointMul

[@CInline]
val point_mul: point_mul_t
let point_mul = point_mul_gen

[@CInline]
val point_mul_g: point_mul_g_t
let point_mul_g res scalar =
  push_frame ();
  let h0 = ST.get () in
  let g = create_point #p384_params in
  make_base_point g;
  point_mul res scalar g;
  admit();
  pop_frame()

[@CInline]
val point_mul_double_g: point_mul_double_g_t
let point_mul_double_g res scalar1 scalar2 p =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create_point #p384_params in
  point_mul_g tmp scalar1;
  point_mul res scalar2 p;
  p384_point_ops.point_add (null uint64) res tmp res;
  admit();
  pop_frame()

inline_for_extraction
instance p384_point_mul_ops : point_mul_ops = {
  point_mul;
  point_mul_g;
  point_mul_double_g
}


