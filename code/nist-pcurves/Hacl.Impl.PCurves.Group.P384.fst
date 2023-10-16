module Hacl.Impl.PCurves.Group.P384

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
open Hacl.Impl.PCurves.Group

[@CInline]
val point_add: point_add_t
let point_add = point_add_g

[@CInline]
val point_double: point_double_t
let point_double = point_double_g

[@CInline]
val point_zero: point_zero_t
let point_zero = point_zero_g

inline_for_extraction
instance p384_point_ops : point_ops = {
  point_add;
  point_double;
  point_zero
}
