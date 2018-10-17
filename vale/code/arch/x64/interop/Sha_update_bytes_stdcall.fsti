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
open SHA_helpers
open Words_s

#set-options "--max_fuel 0 --max_ifuel 1"

let get128_32 (s:Seq.lseq UInt32.t 4) : quad32 =
  Mkfour 
    (UInt32.v (Seq.index s 0))
    (UInt32.v (Seq.index s 1)) 
    (UInt32.v (Seq.index s 2)) 
    (UInt32.v (Seq.index s 3))

let put128_32 (a:quad32) : GTot (Seq.lseq UInt32.t 4) =
  let s0 = UInt32.uint_to_t a.lo0 in
  let s1 = UInt32.uint_to_t a.lo1 in
  let s2 = UInt32.uint_to_t a.hi2 in
  let s3 = UInt32.uint_to_t a.hi3 in  
  Seq.append (Seq.cons s0 (Seq.create 1 s1)) (Seq.cons s2 (Seq.create 1 s3))

let inverses128_32 (u:unit) : Lemma (BV.inverses get128_32 put128_32) =
  let aux (x:Seq.lseq UInt32.t 4) : Lemma (put128_32 (get128_32 x) == x) =
    assert (Seq.equal x (put128_32 (get128_32 x)))
  in Classical.forall_intro aux

let view128_32 = inverses128_32(); BV.View 4 get128_32 put128_32

let pre_cond (h:HS.mem) (ctx_b:B.buffer UInt32.t) (in_b:s8) (num_val:nat64) (k_b:B.buffer UInt32.t) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  M.loc_disjoint (M.loc_buffer ctx_b) (M.loc_buffer k_b) /\ 
  M.loc_disjoint (M.loc_buffer in_b) (M.loc_buffer k_b) /\ 
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length in_b == 64 `op_Multiply` num_val /\
  M.loc_disjoint (M.loc_buffer ctx_b) (M.loc_buffer in_b) /\
  (let k_b128 = BV.mk_buffer_view k_b view128_32 in
  k_reqs (BV.as_seq h k_b128))

let post_cond (h:HS.mem) (h':HS.mem) (ctx_b:B.buffer UInt32.t) (in_b:s8) (num_val:nat64) (k_b:B.buffer UInt32.t) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  live h' ctx_b /\ live h' in_b /\ live h' k_b /\
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length in_b == 64 `op_Multiply` num_val /\
  (let ctx_b128 = BV.mk_buffer_view ctx_b view128_32 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let input_LE = seq_nat8_to_seq_U8 (le_seq_quad32_to_bytes (BV.as_seq h' in_b128)) in
  let hash_in = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h ctx_b128)) in
  let hash_out = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h' ctx_b128)) in
  (Seq.length input_LE) % 64 = 0 /\
  hash_out == update_multi_opaque_vale hash_in input_LE
 )

let full_post_cond (h:HS.mem) (h':HS.mem) (ctx_b:B.buffer UInt32.t) (in_b:s8) (num_val:nat64) (k_b:B.buffer UInt32.t)  =
  post_cond h h' ctx_b in_b num_val k_b  /\
  M.modifies (M.loc_buffer ctx_b) h h'

val sha_update_bytes_stdcall: ctx_b:B.buffer UInt32.t -> in_b:s8 -> num_val:nat64 -> k_b:B.buffer UInt32.t -> Stack unit
	(requires (fun h -> pre_cond h ctx_b in_b num_val k_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 ctx_b in_b num_val k_b ))
