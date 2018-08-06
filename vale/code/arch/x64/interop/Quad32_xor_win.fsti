module Quad32_xor_win

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

unfold let disjoint_or_eq (#a:Type0) (b1:B.buffer a) (b2:B.buffer a) =
  M.(loc_disjoint (loc_buffer b1) (loc_buffer b2)) \/ b1 == b2

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let pre_cond (h:HS.mem) (src1:s8) (src2:s8) (dst:s8) = live h src1 /\ live h src2 /\ live h dst /\ disjoint_or_eq src1 src2 /\ disjoint_or_eq src1 dst /\ disjoint_or_eq src2 dst /\     B.length src1 == 16 /\ B.length src2 == 16 /\ B.length dst == 16

let post_cond (h:HS.mem) (h':HS.mem) (src1:s8) (src2:s8) (dst:s8) =
B.length src1 == 16 /\ B.length src2 == 16 /\ B.length dst == 16 /\
  M.modifies (M.loc_buffer dst) h h' /\
    (let src1 = buffer_to_quad32 src1 h  in
     let src2 = buffer_to_quad32 src2 h  in
     let dst  = buffer_to_quad32 dst  h' in
     dst = quad32_xor src1 src2)

val quad32_xor_buffer_win: src1:s8 -> src2:s8 -> dst:s8 -> Stack unit
        (requires (fun h -> pre_cond h src1 src2 dst ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 src1 src2 dst ))
