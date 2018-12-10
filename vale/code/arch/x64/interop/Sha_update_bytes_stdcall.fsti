module Sha_update_bytes_stdcall

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
open Words.Seq_s
open SHA_helpers
open X64.CPU_Features_s

let uint32_p = B.buffer UInt32.t

unfold
let pre_cond (h:HS.mem) (ctx_b:uint32_p) (in_b:b8) (num_val:UInt64.t) (k_b:uint32_p) =
  let num_val = UInt64.v num_val in
  live h ctx_b /\ live h in_b /\ live h k_b /\
  M.loc_disjoint (M.loc_buffer k_b) (M.loc_buffer ctx_b) /\ 
  M.loc_disjoint (M.loc_buffer k_b) (M.loc_buffer in_b) /\ 
  length k_b == 64 /\
  length ctx_b == 8 /\
  length in_b == 64 `op_Multiply` num_val /\
  M.loc_disjoint (M.loc_buffer ctx_b) (M.loc_buffer in_b) /\
  sha_enabled /\
  (let k_b128 = BV.mk_buffer_view k_b Views.view32_128 in
  k_reqs (BV.as_seq h k_b128))

unfold
let post_cond (h:HS.mem) (h':HS.mem) (ctx_b:uint32_p) (in_b:b8) (num_val:UInt64.t) (k_b:uint32_p) = 
  let num_val = UInt64.v num_val in
  live h ctx_b /\ live h in_b /\ live h k_b /\
  live h' ctx_b /\ live h' in_b /\ live h' k_b /\
  length k_b == 64 /\
  length ctx_b == 8 /\
  length in_b == 64 `op_Multiply` num_val /\
  length ctx_b % 4 == 0 /\
  length in_b % 16 == 0 /\
  (let input_LE = B.as_seq h' in_b in
  let hash_in = B.as_seq h ctx_b in
  let hash_out = B.as_seq h' ctx_b in
  (Seq.length input_LE) % 64 = 0 /\
  (reveal_word ();
  hash_out == update_multi_transparent hash_in input_LE)
 )

unfold
let full_post_cond (h:HS.mem) (h':HS.mem) (ctx_b:uint32_p) (in_b:b8) (num_val:UInt64.t) (k_b:uint32_p)  =
  post_cond h h' ctx_b in_b num_val k_b  /\
  M.modifies (M.loc_buffer ctx_b) h h'

[@ (CCConv "stdcall") ]
val sha256_update: ctx_b:uint32_p -> in_b:b8 -> num_val:UInt64.t -> k_b:uint32_p -> Stack unit
	(requires (fun h -> pre_cond h ctx_b in_b num_val k_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 ctx_b in_b num_val k_b ))
