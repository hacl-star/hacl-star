module X64.BufferViewStore

open Views
open Interop
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open BufferViewHelpers

open X64.Machine_s
open X64.Bytes_Semantics_s

val bv_upd_update_heap64:
  (b:s8{B.length b % 8 == 0}) ->
  (heap:heap) ->
  (i:nat{i < B.length b / 8}) ->
  (v:nat64) ->
  (addrs:addr_map) ->
  (ptrs:list s8) ->
  (h:HS.mem{B.live h b}) ->
   Lemma (
     let bv = BV.mk_buffer_view b view64 in
     BV.as_buffer_mk_buffer_view b view64;
     BV.get_view_mk_buffer_view b view64;
     BV.length_eq bv;
     let heap' = update_heap64 (addrs b + 8 `op_Multiply` i) v heap in
     BV.upd h bv i (UInt64.uint_to_t v) == B.g_upd_seq b (get_seq_heap heap' addrs b) h)

val bv_upd_update_heap128:
  (b:s8{B.length b % 16 == 0}) ->
  (heap:heap) ->
  (i:nat{i < B.length b / 16}) ->
  (v:quad32) ->
  (addrs:addr_map) ->
  (ptrs:list s8) ->
  (h:HS.mem{B.live h b}) ->
   Lemma (
     let bv = BV.mk_buffer_view b view128 in
     BV.as_buffer_mk_buffer_view b view128;
     BV.get_view_mk_buffer_view b view128;
     BV.length_eq bv;
     let heap' = update_heap128 (addrs b + 16 `op_Multiply` i) v heap in
     BV.upd h bv i v == B.g_upd_seq b (get_seq_heap heap' addrs b) h)
