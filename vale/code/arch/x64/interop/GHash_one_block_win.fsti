module GHash_one_block_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls
open GHash

let s8 = B.buffer S8.t

let rec loc_locs_disjoint_rec (l:s8) (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list s8) : Type0 = normalize (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:s8) (ls:list s8) : Type0 = normalize (loc_locs_disjoint_rec b ls)

open FStar.Mul


let buffer_to_quad32 (b:s8{ B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad32 (b:s8{ B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let pre_cond (h:HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:nat64) = live h h_b /\ live h hash_b /\ live h input_b /\ bufs_disjoint [h_b;hash_b;input_b] /\ length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
  B.length h_b >= 16 /\ B.length hash_b >= 16 /\ B.length input_b >= 16 * (offset + 1)

let partial_post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:nat64) = length h_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length input_b % 16 == 0 /\
 B.length h_b >= 16 /\ B.length hash_b >= 16 /\ B.length input_b >= 16 * (offset + 1) /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let input    = buffer_to_seq_quad32 input_b h in
     let input_quad = Seq.index input offset in
     new_hash == ghash_incremental h_q old_hash (Seq.create 1 input_quad)
    )


let post_cond (h:HS.mem) (h':HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (offset:nat64) =
    M.modifies (M.loc_buffer hash_b) h h' /\
    partial_post_cond h h' h_b hash_b input_b offset


val ghash_incremental_one_block_buffer_win: h_b:s8 -> hash_b:s8 -> input_b:s8 -> offset:UInt64.t -> Stack unit
        (requires (fun h -> pre_cond h h_b hash_b input_b (UInt64.v offset) ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 h_b hash_b input_b (UInt64.v offset) ))
