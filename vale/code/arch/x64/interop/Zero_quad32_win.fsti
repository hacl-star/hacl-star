module Zero_quad32_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
module S8 = SecretByte
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls

let b8 = B.buffer UInt8.t
let s8 = B.buffer S8.t

let pre_cond (h:HS.mem) (b:s8) = B.live h b /\
    B.length b == 16

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0


let post_cond (h:HS.mem) (h':HS.mem) (b:s8) = length b == 16 /\
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 0 0 0 0)

val zero_quad32_buffer_win: b:s8 -> Stack unit
        (requires (fun h -> pre_cond h b ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 b ))
