module Hacl.Impl.P256.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val solinas_reduction_impl: f:lbuffer uint64 8ul -> res:lbuffer uint64 4ul -> Stack unit
  (requires fun h -> live h f /\ live h res /\ disjoint f res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 f % S.prime)
