module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Point

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val point_double: res:point -> p:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res)  h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
      S.point_double (from_mont_point (as_point_nat h0 p)))
