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
open Words_s
open Types_s
open SHA_helpers

let pre_cond (h:HS.mem) (ctx_b:s8) (in_b:s8) (num_val:nat64) (k_b:s8) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  disjoint_or_eq ctx_b k_b /\ 
  disjoint_or_eq in_b k_b /\ 
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length in_b == 64 `op_Multiply` num_val /\
  disjoint ctx_b in_b /\
  (let k_b128 = BV.mk_buffer_view k_b Views.view128 in
  k_reqs (BV.as_seq h k_b128))

let post_cond (h:HS.mem) (h':HS.mem) (ctx_b:s8) (in_b:s8) (num_val:nat64) (k_b:s8) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  live h' ctx_b /\ live h' in_b /\ live h' k_b /\
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length in_b == 64 `op_Multiply` num_val /\
  (let ctx_b128 = BV.mk_buffer_view ctx_b Views.view128 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let input_LE = seq_nat8_to_seq_U8 (le_seq_quad32_to_bytes (BV.as_seq h' in_b128)) in
  let hash_in = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h ctx_b128)) in
  let hash_out = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h' ctx_b128)) in
  (Seq.length input_LE) % 64 = 0 /\
  hash_out == update_multi_opaque_vale hash_in input_LE
 )

let full_post_cond (h:HS.mem) (h':HS.mem) (ctx_b:s8) (in_b:s8) (num_val:nat64) (k_b:s8) = 
  post_cond h h' ctx_b in_b num_val k_b /\
  M.modifies (M.loc_buffer ctx_b) h h'

val sha_update_bytes_stdcall: ctx_b:s8 -> in_b:s8 -> num_val:nat64 -> k_b:s8 -> Stack unit
	(requires (fun h -> pre_cond h ctx_b in_b num_val k_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 ctx_b in_b num_val k_b ))
