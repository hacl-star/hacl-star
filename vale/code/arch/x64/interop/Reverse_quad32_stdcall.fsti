module Reverse_quad32_stdcall

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

let pre_cond (h:HS.mem) (b:s8) = live h b /\ length b == 16

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let post_cond (h:HS.mem) (h':HS.mem) (b:s8) =
  length b == 16 /\
  (let old_b = buffer_to_quad32 b h  in
   let new_b = buffer_to_quad32 b h' in
   new_b == reverse_bytes_quad32 old_b)

let full_post_cond (h:HS.mem) (h':HS.mem) (b:s8)  =
  post_cond h h' b  /\
  M.modifies (M.loc_buffer b) h h'

val reverse_quad32_stdcall: b:s8 -> Stack unit
	(requires (fun h -> pre_cond h b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 b ))
