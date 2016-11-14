module Hacl.EC.Curve25519.Bignum.Fscalar

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
open Hacl.EC.Curve25519.Bignum.Fscalar.Lemmas

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64


val fscalar_:
  res:bigint_wide ->
  a:bigint{disjoint res a} ->
  s:s64 ->
  Stack unit
    (requires (fun h -> live h res /\ norm h a))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1 /\ isScalarMult h0 h1 res a s))
let fscalar_ res a s =
  Math.Lemmas.pow2_lt_compat 64 51; Math.Lemmas.pow2_plus 51 64; Math.Lemmas.pow2_plus 64 64;
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let open Hacl.UInt128 in
  let r0 = a0 *^ s in
  let r1 = a1 *^ s in
  let r2 = a2 *^ s in
  let r3 = a3 *^ s in
  let r4 = a4 *^ s in
  update_wide_5 res r0 r1 r2 r3 r4


val scalar': res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> STL unit
     (requires (fun h -> norm h a /\ live h res))
     (ensures (fun h0 u h1 ->
       live h0 res /\ live h1 res /\ norm h0 a /\ norm h1 a
       /\ modifies_1 res h0 h1
       /\ bound115 h1 res
       /\ eval_wide h1 res norm_length = eval h0 a norm_length * v s ))
let scalar' res a s =
  let h0 = ST.get() in
  fscalar_ res a s;
  let h1 = ST.get() in
  lemma_fscalar h0 h1 res a s
