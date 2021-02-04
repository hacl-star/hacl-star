module Hacl.Impl.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.SolinasReduction.Lemmas
open Hacl.Impl.P256.LowLevel 

open Spec.P256.Definitions
open Hacl.Impl.P256.Definition
open FStar.Mul


val solinas_reduction_impl: i: lbuffer uint64 (size 8) -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ wide_as_nat h0 i % prime == as_nat h1 o)
