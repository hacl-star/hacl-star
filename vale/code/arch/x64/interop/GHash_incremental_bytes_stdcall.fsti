module GHash_incremental_bytes_stdcall

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
open AES_s
open GCTR_s
open GCM_s
open GCM_helpers
open GHash
open X64.CPU_Features_s

let pre_cond (h:HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (num_bytes:UInt64.t) = 
  live h h_b /\ live h hash_b /\ live h input_b /\  
  disjoint h_b hash_b /\ 
  disjoint h_b input_b /\ 
  disjoint hash_b input_b /\ 
  length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
  length input_b == 16 `op_Multiply` (bytes_to_quad_size (UInt64.v num_bytes)) /\
  length h_b >= 16 /\
  length hash_b >= 16 /\
  pclmulqdq_enabled

let buffer_to_quad (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  Seq.index (BV.as_seq h b128) 0

let buffer_to_seq_quad (b:s8 { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (num_bytes:UInt64.t) = 
  live h h_b /\ live h hash_b /\ live h input_b /\ 
  live h' h_b /\ live h' hash_b /\ live h' input_b /\
  length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
  length input_b == 16 `op_Multiply` (bytes_to_quad_size (UInt64.v num_bytes)) /\
  length h_b >= 16 /\
  length hash_b >= 16 /\  
  (let old_hash = buffer_to_quad hash_b h  in
   let new_hash = buffer_to_quad hash_b h' in
   let h_q      = buffer_to_quad h_b    h  in
   let num_bytes = UInt64.v num_bytes in
   (num_bytes == 0 ==> new_hash == old_hash) /\
   (let input_bytes = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad input_b h)) 0 num_bytes in
    let padded_bytes = pad_to_128_bits input_bytes in
    let input_quads = le_bytes_to_seq_quad32 padded_bytes in
    num_bytes > 0 ==>
      Seq.length input_quads > 0 /\
      new_hash == ghash_incremental h_q old_hash input_quads
   )
   )  


let full_post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (num_bytes:UInt64.t)  =
  post_cond h h' h_b hash_b input_b num_bytes  /\
  M.modifies (M.loc_buffer hash_b) h h'

val ghash_incremental_bytes_stdcall: h_b:s8 -> hash_b:s8 -> input_b:s8 -> num_bytes:UInt64.t -> Stack unit
	(requires (fun h -> pre_cond h h_b hash_b input_b num_bytes ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 h_b hash_b input_b num_bytes ))
