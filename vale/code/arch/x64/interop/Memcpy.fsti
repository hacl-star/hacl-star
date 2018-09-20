module Memcpy

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls

let pre_cond (h:HS.mem) (dst:s8) (src:s8) = live h dst /\ live h src /\ bufs_disjoint [dst;src] /\ length dst % 8 == 0 /\ length src % 8 == 0 /\ length dst == 16 /\ length src == 16

let post_cond (h0:HS.mem) (h1:HS.mem) (dst:s8) (src:s8) = live h0 dst /\ live h0 src /\ live h1 dst /\ live h1 src /\ length dst % 8 == 0 /\ length src % 8 == 0 /\
  (let dst_b = BV.mk_buffer_view dst Views.view64 in
  let src_b = BV.mk_buffer_view src Views.view64 in
  Seq.equal (BV.as_seq h1 dst_b) (BV.as_seq h1 src_b))

val memcpy: dst:s8 -> src:s8 -> Stack unit
	(requires (fun h -> pre_cond h dst src ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 dst src ))
