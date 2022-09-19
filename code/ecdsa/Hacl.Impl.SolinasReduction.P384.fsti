module Hacl.Impl.SolinasReduction.P384


open FStar.HyperStack.All
open FStar.HyperStack

module ST = FStar.HyperStack.ST

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.EC.Definition

[@CInline]
val solinas_reduction_impl_p384: i: lbuffer uint64 (size 12) -> o: lbuffer uint64 (size 6) -> 
  Stack unit 
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ wide_as_nat P384 h0 i % prime384 = as_nat P384 h1 o)
