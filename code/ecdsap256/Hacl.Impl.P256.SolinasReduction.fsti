module Hacl.Impl.P256.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val solinas_reduction_impl: f:lbuffer uint64 (size 8) -> res:lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h f /\ live h res /\ disjoint f res)
  (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
    as_nat h1 res == wide_as_nat h0 f % prime256)
