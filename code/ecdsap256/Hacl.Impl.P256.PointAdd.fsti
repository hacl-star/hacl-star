module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum
open Hacl.Impl.P256.Point

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val point_add: p:point -> q:point -> res:point -> tmp:lbuffer uint64 (size 88) -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h res /\ live h tmp /\
    eq_or_disjoint q res /\ disjoint p q /\ disjoint p tmp /\
    disjoint q tmp /\ disjoint p res /\ disjoint res tmp /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc tmp |+| loc res) h0 h1 /\
    point_inv h1 res /\
    SM.fromDomainPoint (as_point_nat h1 res) ==
    S.point_add (SM.fromDomainPoint (as_point_nat h0 p)) (SM.fromDomainPoint (as_point_nat h0 q)))
