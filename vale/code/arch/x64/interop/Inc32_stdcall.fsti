module Inc32_stdcall

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
open GCTR_s

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let pre_cond (h:HS.mem) (iv_b:s8) =
  live h iv_b /\ length iv_b == 16

let post_cond (h:HS.mem) (h':HS.mem) (iv_b:s8) = 
  live h iv_b /\ live h' iv_b /\ length iv_b == 16 /\
  (let old_iv = buffer_to_quad32 iv_b h  in
   let new_iv = buffer_to_quad32 iv_b h' in
   new_iv == inc32 old_iv 1)  

let full_post_cond (h:HS.mem) (h':HS.mem) (iv_b:s8)  =
  post_cond h h' iv_b  /\
  M.modifies (M.loc_buffer iv_b) h h'

val inc32_stdcall: iv_b:s8 -> Stack unit
	(requires (fun h -> pre_cond h iv_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 iv_b ))
