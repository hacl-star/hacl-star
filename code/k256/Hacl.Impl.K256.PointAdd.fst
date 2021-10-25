module Hacl.Impl.K256.PointAdd

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module S = Spec.K256

open Hacl.K256.Field
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


val point_add (out p q:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    eq_or_disjoint out p /\ eq_or_disjoint out q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_inv h1 out /\
    point_as_nat3_proj h1 out == S.point_add (point_as_nat3_proj h0 p) (point_as_nat3_proj h0 q))
