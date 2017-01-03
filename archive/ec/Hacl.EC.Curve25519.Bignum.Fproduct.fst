module Hacl.EC.Curve25519.Bignum.Fproduct

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Math.Lib
open FStar.Math.Lemmas
open FStar.Buffer
open FStar.Buffer.Quantifiers

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

private val multiplication_0:
  c:bigint_wide{length c >= 2*norm_length-1} ->
  a0:H64.t -> a1:H64.t -> a2:H64.t -> a3:H64.t -> a4:H64.t ->
  b0:H64.t -> b1:H64.t -> b2:H64.t -> b3:H64.t -> b4:H64.t ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
let multiplication_0 c a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  let open Hacl.UInt128 in
  let ab00 = a0 *^ b0 in
  let ab01 = a0 *^ b1 in
  let ab02 = a0 *^ b2 in
  let ab03 = a0 *^ b3 in
  let ab04 = a0 *^ b4 in
  let ab10 = a1 *^ b0 in
  let ab11 = a1 *^ b1 in
  let ab12 = a1 *^ b2 in
  let ab13 = a1 *^ b3 in
  let ab14 = a1 *^ b4 in
  let ab20 = a2 *^ b0 in
  let ab21 = a2 *^ b1 in
  let ab22 = a2 *^ b2 in
  let ab23 = a2 *^ b3 in
  let ab24 = a2 *^ b4 in
  let ab30 = a3 *^ b0 in
  let ab31 = a3 *^ b1 in
  let ab32 = a3 *^ b2 in
  let ab33 = a3 *^ b3 in
  let ab34 = a3 *^ b4 in
  let ab40 = a4 *^ b0 in
  let ab41 = a4 *^ b1 in
  let ab42 = a4 *^ b2 in
  let ab43 = a4 *^ b3 in
  let ab44 = a4 *^ b4 in
  let open Hacl.UInt64 in
  let c0 = ab00 in
  let c1 = H128.(ab01 +%^ ab10) in
  let c2 = H128.(ab02 +%^ ab11 +%^ ab20) in
  let c3 = H128.(ab03 +%^ ab12 +%^ ab21 +%^ ab30) in
  let c4 = H128.(ab04 +%^ ab13 +%^ ab22 +%^ ab31 +%^ ab40) in
  let c5 = H128.(ab14 +%^ ab23 +%^ ab32 +%^ ab41) in
  let c6 = H128.(ab24 +%^ ab33 +%^ ab42) in
  let c7 = H128.(ab34 +%^ ab43) in
  let c8 = ab44 in
  update_wide_9 c c0 c1 c2 c3 c4 c5 c6 c7 c8


private val multiplication_:
  c:bigint_wide{length c >= 2 * norm_length - 1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c))
     (ensures (fun h0 u h1 -> live h1 c /\ modifies_1 c h0 h1))
let multiplication_ c a b =
  let h0 = ST.get() in
  let a0 = a.(0ul) in let a1 = a.(1ul) in let a2 = a.(2ul) in let a3 = a.(3ul) in let a4 = a.(4ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in let b2 = b.(2ul) in let b3 = b.(3ul) in let b4 = b.(4ul) in
  multiplication_0 c a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


val multiplication:
  c:bigint_wide{length c >= 2 * norm_length - 1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c))
     (ensures (fun h0 u h1 -> live h1 c /\ modifies_1 c h0 h1))
let multiplication c a b =
  multiplication_ c a b
