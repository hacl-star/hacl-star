module Hacl.Impl.PCurves.InvSqrt

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field

module S = Spec.PCurves
module CC = Hacl.Impl.PCurves.Constants

class curve_inv_sqrt {| S.curve_params |} = {
  finv: res:felem -> a:felem -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ eq_or_disjoint a res /\
      as_nat h a < S.prime)
    (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
      as_nat h1 res < S.prime /\
      CC.fmont_as_nat h1 res = S.finv (CC.fmont_as_nat h0 a));
  fsqrt: res:felem -> a:felem -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ eq_or_disjoint a res /\
      as_nat h a < S.prime)
    (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
      as_nat h1 res < S.prime /\
      CC.fmont_as_nat h1 res = S.fsqrt (CC.fmont_as_nat h0 a));
   qinv: res:felem -> a:felem -> Stack unit
   (requires fun h ->
     live h a /\ live h res /\ eq_or_disjoint a res /\
     as_nat h a < S.order)
   (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
     as_nat h1 res < S.order /\
     CC.qmont_as_nat h1 res == S.qinv (CC.qmont_as_nat h0 a))
}

