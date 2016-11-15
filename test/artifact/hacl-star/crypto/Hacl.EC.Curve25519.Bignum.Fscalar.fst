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
    (requires (fun h -> live h res /\ live h a))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1))
let fscalar_ res a s =
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
     (requires (fun h -> live h a /\ live h res))
     (ensures (fun h0 u h1 -> live h1 res /\ modifies_1 res h0 h1))
let scalar' res a s =
  fscalar_ res a s
