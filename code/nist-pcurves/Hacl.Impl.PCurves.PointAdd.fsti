module Hacl.Impl.PCurves.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

module S = Spec.PCurves

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

noextract inline_for_extraction
val point_add {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| f:field_ops |} {| curve_inv_sqrt|}:
  res:point -> p:point -> q:point -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\
    eq_or_disjoint p q /\ eq_or_disjoint q res /\ eq_or_disjoint p res /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
    S.point_add (from_mont_point (as_point_nat h0 p)) (from_mont_point (as_point_nat h0 q)))
