module Vale.AsLowStar.MemoryHelpers

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module MES = X64.Memory_Sems
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = X64.Vale.StateLemmas
module VL = X64.Vale.Lemmas
module ST = FStar.HyperStack.ST

val buffer_readable_reveal 
  (bt:ME.base_typ)
  (x:lowstar_buffer (ME.TBase bt)) 
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer{mem_roots_p h0 (arg_of_lb stack::args)}) : Lemma (
    let mem = Interop.Adapters.mk_mem (arg_of_lb stack::args) h0 in
    ME.buffer_readable mem (as_vale_buffer #(ME.TBase bt) x) <==>
      List.memP x (Interop.Adapters.ptrs_of_mem mem))

val get_heap_mk_mem_reveal
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer{mem_roots_p h0 (arg_of_lb stack::args)}) : Lemma
  (let mem = Interop.Adapters.mk_mem (arg_of_lb stack::args) h0 in
   Interop.Adapters.liveness_disjointness (arg_of_lb stack::args) h0;
   MES.get_heap mem == IM.down_mem h0 IA.addrs (Interop.Adapters.args_b8 (arg_of_lb stack::args)))

val buffer_as_seq_reveal
  (t:ME.base_typ)
  (x:lowstar_buffer (ME.TBase t))
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer{mem_roots_p h0 (arg_of_lb stack::args)}) : Lemma
  (let y = as_vale_buffer x in
  let mem = Interop.Adapters.mk_mem (arg_of_lb stack::args) h0 in
  assume (t <> ME.TUInt128); // TODO: UInt128
  Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq mem y))
    (BV.as_seq h0 (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val buffer_addr_reveal
  (t:ME.base_typ)
  (x:lowstar_buffer (ME.TBase t))
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = Interop.Adapters.mk_mem args h0 in
  IA.addrs x == ME.buffer_addr (as_vale_buffer #(ME.TBase t) x) mem)
