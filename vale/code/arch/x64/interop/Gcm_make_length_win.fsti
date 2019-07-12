module Gcm_make_length_win

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


let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let pre_cond (h:HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8) =
    B.live h b /\
    B.length b == 16 /\
    8 * plain_num_bytes < pow2_32 /\
    8 * auth_num_bytes < pow2_32

let post_cond (h:HS.mem) (h':HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8) =
    8 * plain_num_bytes < pow2_32 /\
    8 * auth_num_bytes < pow2_32 /\
  length b == 16 /\     M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == reverse_bytes_quad32 (Mkfour (8 * plain_num_bytes) 0 (8 * auth_num_bytes) 0))

val gcm_make_length_quad_buffer_win: plain_num_bytes:UInt64.t -> auth_num_bytes:UInt64.t -> b:s8 -> Stack unit
        (requires (fun h -> pre_cond h (UInt64.v plain_num_bytes) (UInt64.v auth_num_bytes) b ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 (UInt64.v plain_num_bytes) (UInt64.v auth_num_bytes) b ))
