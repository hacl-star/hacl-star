module Hacl.Impl.EC.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Impl.P256.LowLevel 

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition
open FStar.Mul


val reduction: #c: curve 
  -> i: lbuffer uint64 (getCoordinateLenU64 c *. 2ul) 
  -> o: lbuffer uint64 (getCoordinateLenU64 c) -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ wide_as_nat c h0 i % (getPrime c) == as_nat c h1 o)