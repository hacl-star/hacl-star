module Hacl.Impl.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Constants
open Hacl.Spec.P256.Felem
open Hacl.SolinasReduction.Lemmas

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val solinas_reduction_impl: i: lbuffer uint64 (size 8) -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ wide_as_nat h0 i % prime == as_nat h1 o)
