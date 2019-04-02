module Hacl.EC.Curve25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open Hacl.UInt8
open Hacl.Cast
open FStar.Buffer


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module B  = FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

type bigint = buffer H64.t
type uint8_p = buffer H8.t

val exp: output:uint8_p{length output >= 32} -> q_x:uint8_p{length q_x >= 32 /\ disjoint q_x output} ->
  pk:uint8_p{length pk >= 32 /\ disjoint pk output /\ disjoint pk q_x} -> STL unit
  (requires (fun h -> B.live h output /\ B.live h q_x /\ B.live h pk))
  (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ B.live h1 output))
