module Vale.X64.BufferViewStore

open Vale.Interop.Views
open Vale.Interop
module MB = LowStar.Monotonic.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module HS = FStar.HyperStack
open Vale.Lib.BufferViewHelpers
open FStar.Mul

open Vale.X64.Machine_s
open Vale.X64.Machine_Semantics_s
module ME = Vale.X64.Memory
module IB = Vale.Interop.Base

val bv_upd_update_heap64:
  (b:IB.b8{DV.length (IB.get_downview b.IB.bsrc) % 8 == 0}) ->
  (heap:machine_heap) ->
  (i:nat{i < DV.length (IB.get_downview b.IB.bsrc) / 8}) ->
  (v:nat64) ->
  (mem:IB.interop_heap{MB.live (IB.hs_of_mem mem) b.IB.bsrc}) ->
   Lemma
     (requires IB.correct_down_p mem heap b)
     (ensures
       (let dv = IB.get_downview b.IB.bsrc in
        let bv = UV.mk_buffer dv up_view64 in
        let addrs = IB.addrs_of_mem mem in
        let h = IB.hs_of_mem mem in
        UV.length_eq bv;
        let heap' = update_heap64 (addrs b + 8 * i) v heap in
        UV.upd h bv i (UInt64.uint_to_t v) == DV.upd_seq h dv (get_seq_heap heap' addrs b)))

val bv_upd_update_heap128:
  (b:IB.b8{DV.length (IB.get_downview b.IB.bsrc) % 16 == 0}) ->
  (heap:machine_heap) ->
  (i:nat{i < DV.length (IB.get_downview b.IB.bsrc) / 16}) ->
  (v:quad32) ->
  (mem:IB.interop_heap{MB.live (IB.hs_of_mem mem) b.IB.bsrc}) ->
   Lemma
     (requires IB.correct_down_p mem heap b)
     (ensures
       (let dv = IB.get_downview b.IB.bsrc in
        let bv = UV.mk_buffer dv up_view128 in
        let addrs = IB.addrs_of_mem mem in
        let h = IB.hs_of_mem mem in
        UV.length_eq bv;
        let heap' = update_heap128 (addrs b + 16 * i) v heap in
        UV.upd h bv i v == DV.upd_seq h dv (get_seq_heap heap' addrs b)))
