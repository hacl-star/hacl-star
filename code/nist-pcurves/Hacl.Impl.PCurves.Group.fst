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

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let point_add_g ctx x y xy =
  let h0 = ST.get () in
  SL.to_aff_point_add_lemma
    (from_mont_point (as_point_nat h0 x)) (from_mont_point (as_point_nat h0 y));
  Hacl.Impl.PCurves.PointAdd.point_add xy x y


let point_double_g ctx x xx =
  let h0 = ST.get () in
  SL.to_aff_point_double_lemma (from_mont_point (as_point_nat h0 x));
  Hacl.Impl.PCurves.PointDouble.point_double xx x


let point_zero_g {| cp:S.curve_params |} ctx one =
  let h0 = ST.get () in
  SL.to_aff_point_at_infinity_lemma #cp;
  make_point_at_inf one

