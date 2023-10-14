module Hacl.Impl.PCurves.PointMul.P256

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

open Spec.P256
open Hacl.Impl.PCurves.Constants.P256
open Hacl.Impl.PCurves.Bignum.P256
open Hacl.Impl.PCurves.Field.P256
open Hacl.Impl.PCurves.Finv.P256
open Hacl.Impl.PCurves.Qinv.P256
open Hacl.Impl.PCurves.Group.P256
open Hacl.Impl.PCurves.PrecompTable.P256
open Hacl.Impl.PCurves.PointMul

[@CInline]
val point_mul: point_mul_t
let point_mul = point_mul_gen

[@CInline]
val point_mul_g: point_mul_g_t
let point_mul_g = point_mul_g_gen

[@CInline]
val point_mul_double_g: point_mul_double_g_t
let point_mul_double_g = point_mul_double_g_gen

inline_for_extraction
instance p256_point_mul_ops : point_mul_ops = {
  point_mul;
  point_mul_g;
  point_mul_double_g
}


