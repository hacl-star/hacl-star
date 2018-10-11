module Gcm_make_length_stdcall

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
open Words_s

let pre_cond (h:HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8) = 
  live h b /\ length b == 16 /\
  8 `op_Multiply` plain_num_bytes < pow2_32 /\
  8 `op_Multiply` auth_num_bytes < pow2_32

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let post_cond (h:HS.mem) (h':HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8) =
  length b == 16 /\
  8 `op_Multiply` plain_num_bytes < pow2_32 /\
  8 `op_Multiply` auth_num_bytes < pow2_32 /\
  (let new_b = buffer_to_quad32 b h' in
   new_b == reverse_bytes_quad32 
     (Mkfour (8 `op_Multiply` plain_num_bytes) 0 (8 `op_Multiply` auth_num_bytes) 0))

let full_post_cond (h:HS.mem) (h':HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8)  =
  post_cond h h' plain_num_bytes auth_num_bytes b  /\
  M.modifies (M.loc_buffer b) h h'

val gcm_make_length_stdcall: plain_num_bytes:nat64 -> auth_num_bytes:nat64 -> b:s8 -> Stack unit
	(requires (fun h -> pre_cond h plain_num_bytes auth_num_bytes b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 plain_num_bytes auth_num_bytes b ))
