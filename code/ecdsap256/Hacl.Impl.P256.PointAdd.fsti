module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Point

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val point_add: res:point -> p:point -> q:point -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\
    eq_or_disjoint p q /\ eq_or_disjoint q res /\ eq_or_disjoint p res /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
    S.point_add (from_mont_point (as_point_nat h0 p)) (from_mont_point (as_point_nat h0 q)))
