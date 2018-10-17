module GHash_one_block

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
open X64.CPU_Features_s
open GHash

let buffer_to_quad32 (b:s8{ B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let buffer_to_seq_quad32 (b:s8{ B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let pre_cond (h:HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:UInt64.t) = 
  pclmulqdq_enabled /\
  live h h_b /\ live h hash_b /\ live h input_b /\
  disjoint h_b hash_b /\ 
  disjoint h_b input_b /\ 
  disjoint hash_b input_b /\ 
  length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
  length h_b >= 16 /\ length hash_b >= 16 /\ length input_b >= 16 `op_Multiply` ((UInt64.v offset) + 1)  

let post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:UInt64.t) = 
  live h h_b /\ live h hash_b /\ live h input_b /\
  live h' h_b /\ live h' hash_b /\ live h' input_b /\ 
  length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
  length h_b >= 16 /\ length hash_b >= 16 /\ length input_b >= 16 `op_Multiply` ((UInt64.v offset) + 1) /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let input    = buffer_to_seq_quad32 input_b h in
     let input_quad = Seq.index input (UInt64.v offset) in
     new_hash == ghash_incremental h_q old_hash (Seq.create 1 input_quad)
    )  

let full_post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:UInt64.t)  =
  post_cond h h' h_b hash_b input_b offset  /\
  M.modifies (M.loc_buffer hash_b) h h'

val ghash_one_block: h_b:s8 -> hash_b:s8 -> input_b:s8 -> offset:UInt64.t -> Stack unit
	(requires (fun h -> pre_cond h h_b hash_b input_b offset ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 h_b hash_b input_b offset ))
