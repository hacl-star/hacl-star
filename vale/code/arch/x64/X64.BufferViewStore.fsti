module X64.BufferViewStore

open Views
open Interop
module MB = LowStar.Monotonic.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open BufferViewHelpers

open X64.Machine_s
open X64.Bytes_Semantics_s
module ME = X64.Memory
module IB = Interop.Base

val bv_upd_update_heap64:
  (b:IB.b8{MB.length b.IB.b % 8 == 0}) ->
  (heap:heap) ->
  (i:nat{i < MB.length b.IB.b / 8}) ->
  (v:nat64) ->
  (mem:IB.mem{MB.live (IB.hs_of_mem mem) b.IB.b}) ->
   Lemma
     (requires IB.correct_down_p mem heap b)
     (ensures 
       (let bv = BV.mk_buffer_view b.IB.b view64 in
        let addrs = IB.addrs_of_mem mem in
        let h = IB.hs_of_mem mem in
        BV.as_buffer_mk_buffer_view b.IB.b view64;
        BV.get_view_mk_buffer_view b.IB.b view64;
        BV.length_eq bv;
        let heap' = update_heap64 (addrs b + 8 `op_Multiply` i) v heap in
        BV.upd h bv i (UInt64.uint_to_t v) == MB.g_upd_seq b.IB.b (get_seq_heap heap' addrs b) h))

val bv_upd_update_heap128:
  (b:IB.b8{MB.length b.IB.b % 16 == 0}) ->
  (heap:heap) ->
  (i:nat{i < MB.length b.IB.b / 16}) ->
  (v:quad32) ->
  (mem:IB.mem{MB.live (IB.hs_of_mem mem) b.IB.b}) ->
   Lemma 
     (requires IB.correct_down_p mem heap b)
     (ensures (
       let bv = BV.mk_buffer_view b.IB.b view128 in
       let addrs = IB.addrs_of_mem mem in
       let h = IB.hs_of_mem mem in
       BV.as_buffer_mk_buffer_view b.IB.b view128;
       BV.get_view_mk_buffer_view b.IB.b view128;
       BV.length_eq bv;
       let heap' = update_heap128 (addrs b + 16 `op_Multiply` i) v heap in
       BV.upd h bv i v == MB.g_upd_seq b.IB.b (get_seq_heap heap' addrs b) h))
