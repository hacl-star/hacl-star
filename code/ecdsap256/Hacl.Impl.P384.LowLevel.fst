module Hacl.Impl.P384.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
(* open Spec.ECDSA.Lemmas *)
open Spec.P256
open Spec.ECDSA

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

(* open Spec.P256.Lemmas *)
open Lib.IntTypes.Intrinsics


val mul_p384: f: felem P384 -> r: felem P384 -> out: widefelem P384 -> 
  Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r /\ disjoint r out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      wide_as_nat P384 h1 out = as_nat P384 h0 r * as_nat P384 h0 f
    )

let mul_p384 f r out = admit()


val square_p384: f: felem P384 -> out: widefelem P384 -> Stack unit
    (requires fun h -> live h out /\ live h f /\ eq_or_disjoint f out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ wide_as_nat P384 h1 out = as_nat P384 h0 f * as_nat P384 h0 f)

let square_p384 f out = admit()
