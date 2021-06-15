module Hacl.Impl.EC.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open FStar.Mul
//open Hacl.Spec.MontgomeryMultiplication

//open Hacl.Impl.EC.Setup


#set-options "--z3rlimit 100"


inline_for_extraction noextract
val mul: #c: curve -> f: felem c -> r: felem c -> out: widefelem c ->
  Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r /\ disjoint r out /\ disjoint f out /\ eq_or_disjoint f r)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 )


val mul_p256: f: felem P256 -> r: felem P256 -> out: widefelem P256 ->
  Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r /\ disjoint r out /\ disjoint f out /\ eq_or_disjoint f r)
    (ensures  fun h0 _ h1 -> True)