module Quad32_xor_stdcall

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Types_s

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let pre_cond (h:HS.mem) (src1:s8) (src2:s8) (dst:s8) = 
  live h src1 /\ live h src2 /\ live h dst /\ 
  disjoint_or_eq src1 src2 /\ 
  disjoint_or_eq src1 dst /\ 
  disjoint_or_eq src2 dst /\ 
  length src1 == 16 /\ length src2 == 16 /\ length dst == 16

let post_cond (h:HS.mem) (h':HS.mem) (src1:s8) (src2:s8) (dst:s8) = 
  live h src1 /\ live h src2 /\ live h dst /\ 
  live h' src1 /\ live h' src2 /\ live h' dst /\ 
  length src1 == 16 /\ length src2 == 16 /\ length dst == 16 /\
  (let src1 = buffer_to_quad32 src1 h  in
   let src2 = buffer_to_quad32 src2 h  in
   let dst  = buffer_to_quad32 dst  h' in
   dst = quad32_xor src1 src2)  

let full_post_cond (h:HS.mem) (h':HS.mem) (src1:s8) (src2:s8) (dst:s8)  =
  post_cond h h' src1 src2 dst  /\
  M.modifies (M.loc_buffer dst) h h'

val quad32_xor_stdcall: src1:s8 -> src2:s8 -> dst:s8 -> Stack unit
	(requires (fun h -> pre_cond h src1 src2 dst ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 src1 src2 dst ))
