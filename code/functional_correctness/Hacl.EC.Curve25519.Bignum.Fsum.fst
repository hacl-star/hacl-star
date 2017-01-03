module Hacl.EC.Curve25519.Bignum.Fsum

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Buffer.Quantifiers
(* open Hacl.SBuffer *)
open FStar.Math.Lib
open FStar.Ghost
open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils
open Hacl.EC.Curve25519.Bignum.Fsum.Lemmas

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

private val fsum_:
  a:bigint ->
  b:bigint{disjoint a b} ->
  Stack unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 a /\ modifies_1 a h0 h1
      /\ isSum h0 h1 a b))
let fsum_ a b =
  let h0 = ST.get() in
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
  assert(v a0 = v (get h0 a 0)); assert(v a1 = v (get h0 a 1)); assert(v a2 = v (get h0 a 2));
  assert(v a3 = v (get h0 a 3)); assert(v a4 = v (get h0 a 4)); assert(v b0 = v (get h0 b 0));
  assert(v b1 = v (get h0 b 1)); assert(v b2 = v (get h0 b 2)); assert(v b3 = v (get h0 b 3));
  assert(v b4 = v (get h0 b 4));
  lemma_fsum_0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
  let ab0 = a0 +^ b0 in
  let ab1 = a1 +^ b1 in
  let ab2 = a2 +^ b2 in
  let ab3 = a3 +^ b3 in
  let ab4 = a4 +^ b4 in
  update_5 a ab0 ab1 ab2 ab3 ab4


val fsum':
  a:bigint ->
  b:bigint{disjoint a b} ->
  Stack unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ bound52 h1 a /\ modifies_1 a h0 h1
      /\ isSum h0 h1 a b
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
    ))
let fsum' a b =
  let h0 = ST.get() in
  fsum_ a b;
  let h1 = ST.get() in
  lemma_fsum h0 h1 a b
