module Hacl.EC.Curve25519.Bignum.Fdifference

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils
open Hacl.EC.Curve25519.Bignum.Fdifference.Lemmas

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val add_big_zero_:
  b:bigint ->
  Stack unit
    (requires (fun h -> norm h b))
    (ensures (fun h0 _ h1 -> addedZero h0 h1 b /\ modifies_1 b h0 h1))
let add_big_zero_ b =
  let two52m38 = (Hacl.Cast.uint64_to_sint64 0xfffffffffffdauL) in // pow2 52 - 38
  let two52m2 =  (Hacl.Cast.uint64_to_sint64 0xffffffffffffeuL) in // pow2 52 - 2
  lemma_pow2_52m38 ();
  lemma_pow2_52m2 ();
  cut(v two52m38 = pow2 52 - 38 /\ v two52m2 = pow2 52 - 2);
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  lemma_add_big_zero_core b0 b1 b2 b3 b4;
  let c0 = b0 +^ two52m38 in
  let c1 = b1 +^ two52m2  in
  let c2 = b2 +^ two52m2  in
  let c3 = b3 +^ two52m2  in
  let c4 = b4 +^ two52m2  in
  update_5 b c0 c1 c2 c3 c4


val add_big_zero:
  b:bigint ->
  Stack unit
    (requires (fun h -> norm h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ fits51to53 h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let add_big_zero b =
  let h0 = ST.get() in
  add_big_zero_ b;
  let h1 = ST.get() in
  lemma_add_zero_eval h0 h1 b


val fdifference_:
  a:bigint ->
  b:bigint{disjoint a b} ->
  Stack unit
    (requires (fun h -> norm h a /\ fits51to53 h b))
    (ensures (fun h0 _ h1 -> bound53 h1 a /\ modifies_1 a h0 h1
      /\ isDifference h0 h1 a b))
let fdifference_ a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let c0 = b0 -^ a0 in
  let c1 = b1 -^ a1 in
  let c2 = b2 -^ a2 in
  let c3 = b3 -^ a3 in
  let c4 = b4 -^ a4 in
  update_5 a c0 c1 c2 c3 c4


val fdifference':
  a:bigint ->
  b:bigint{disjoint a b} ->
  Stack unit
    (requires (fun h -> norm h a /\ fits51to53 h b))
    (ensures (fun h0 u h1 -> live h0 a /\ live h0 b /\ bound53 h1 a /\ modifies_1 a h0 h1
      /\ eval h1 a norm_length
        = eval h0 b norm_length - eval h0 a norm_length))
let fdifference' a b =
  let h0 = ST.get() in
  fdifference_ a b;
  let h1 = ST.get() in
  lemma_fdifference h0 h1 a b
