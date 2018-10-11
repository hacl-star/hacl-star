module GHash_extra_stdcall

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open GCTR_s
open GCTR
open GCM_s
open GCM_helpers
open GHash
open X64.CPU_Features_s

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let buffer_to_seq_quad32 (b:s8 { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let pre_cond (h:HS.mem) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:UInt64.t) (orig_hash:Ghost.erased (quad32)) = 
  pclmulqdq_enabled /\
  live h in_b /\ live h hash_b /\ live h h_b /\  
  disjoint in_b hash_b /\ 
  disjoint in_b h_b /\ 
  disjoint hash_b h_b /\ 
  length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
  length in_b == bytes_to_quad_size (UInt64.v num_bytes) `op_Multiply` 16 /\
  length h_b == 16 /\
  length hash_b == 16 /\
  4096 `op_Multiply` (UInt64.v num_bytes) < pow2_32 /\
  256 `op_Multiply` bytes_to_quad_size (UInt64.v num_bytes) < pow2_32 /\

  (let num_bytes = UInt64.v num_bytes in
   let num_blocks = num_bytes / 16 in
   let old_hash = buffer_to_quad32 hash_b h in
   let h_val = buffer_to_quad32 h_b h in
   // GHash reqs
   let input = Seq.slice (buffer_to_seq_quad32 in_b h) 0 num_blocks in
   old_hash == ghash_incremental0 h_val (Ghost.reveal orig_hash) input /\

   // Extra reqs
   num_bytes % 16 <> 0 /\
   0 < num_bytes /\ num_bytes < 16 `op_Multiply` bytes_to_quad_size num_bytes /\
   16 `op_Multiply` (bytes_to_quad_size num_bytes - 1) < num_bytes)

let post_cond (h:HS.mem) (h':HS.mem) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:UInt64.t) (orig_hash:Ghost.erased (quad32)) = 
  live h in_b /\ live h hash_b /\ live h h_b /\
  live h' in_b /\ live h' hash_b /\ live h' h_b /\
  length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
  length in_b  == bytes_to_quad_size (UInt64.v num_bytes) `op_Multiply` 16 /\
  length h_b == 16 /\
  length hash_b == 16 /\
  (let num_bytes = UInt64.v num_bytes in
   let num_blocks = num_bytes / 16 in
   let old_hash = buffer_to_quad32 hash_b h in
   let new_hash = buffer_to_quad32 hash_b h' in
   let h_val = buffer_to_quad32 h_b h in

   let input_bytes = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 in_b h')) 0 num_bytes in
   let padded_bytes = pad_to_128_bits input_bytes in
   let input_quads = le_bytes_to_seq_quad32 padded_bytes in
   (num_bytes > 0 ==> Seq.length input_quads > 0 /\
                       new_hash == ghash_incremental h_val (Ghost.reveal orig_hash) input_quads)
    )  

let full_post_cond (h:HS.mem) (h':HS.mem) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:UInt64.t) (orig_hash:Ghost.erased (quad32))  =
  post_cond h h' in_b hash_b h_b num_bytes orig_hash  /\
  M.modifies (M.loc_buffer hash_b) h h'

val ghash_extra_stdcall: in_b:s8 -> hash_b:s8 -> h_b:s8 -> num_bytes:UInt64.t -> orig_hash:Ghost.erased (quad32) -> Stack unit
	(requires (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 in_b hash_b h_b num_bytes orig_hash ))
