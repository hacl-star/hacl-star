module X64.BufferViewStore

open Views
open Interop
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open BufferViewHelpers

friend LowStar.BufferView
friend SecretByte

(* TODO: Add correct_down_p as hypothesis *)

let bv_upd_update_heap64 b heap i v addrs ptrs h =
  let bv = BV.mk_buffer_view b view64 in
  BV.as_buffer_mk_buffer_view b view64;
  BV.get_view_mk_buffer_view b view64;
  BV.length_eq bv;
  let ptr = addrs b + 8 `op_Multiply` i in
  let heap' = update_heap64 ptr v heap in
  let prefix, _, suffix = BV.split_at_i bv i h in
  let s1 = prefix `Seq.append` (BV.View?.put view64 (UInt64.uint_to_t v) `Seq.append` suffix) in
  assume (correct_down_p h addrs heap b);
  assert (forall (i:nat{i < Seq.length s1}). Seq.index (B.as_seq h b) i == Seq.index (get_seq_heap heap addrs b) i);
  assume (forall (j:nat{j < 8}) . UInt8.v (Seq.index (BV.View?.put view64 (UInt64.uint_to_t v)) j) == heap'.[ptr + j]);
  X64.Bytes_Semantics.frame_update_heap (addrs b + 8 `op_Multiply` i) v heap;
  (* This is the goal. If we prove the following, we can conclude *)
  assume (Seq.equal s1 (get_seq_heap heap' addrs b));
  ()


let bv_upd_update_heap128 b heap i v addrs ptrs h = admit()
