module Hacl.Impl.PCurves.Qinv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Scalar

module S = Spec.PCurves

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val qinv: {| cp:S.curve_params |} -> res:felem -> a:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    qmont_as_nat h1 res == S.qinv (qmont_as_nat h0 a))
