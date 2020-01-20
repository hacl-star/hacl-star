module Vale.X64.MemoryAdapters

open FStar.Mul
open Vale.Interop.Base
open Vale.Arch.HeapTypes_s
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.Arch.MachineHeap_s
module BS = Vale.X64.Machine_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module SI = Vale.X64.Stack_i
module IB = Vale.Interop.Base
module VS = Vale.X64.State
module V = Vale.X64.Decls
module Map16 = Vale.Lib.Map16
val as_vale_buffer (#src #t:base_typ) (i:IB.buf_t src t) : GTot (ME.buffer t)
val as_vale_immbuffer (#src #t:base_typ) (i:IB.ibuf_t src t) : GTot (ME.buffer t)

val stack_eq : squash (BS.machine_stack == SI.vale_stack)

val as_mem (h:ME.vale_heap) : GTot IB.interop_heap

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

val lemma_heap_impl : squash (heap_impl == vale_full_heap)

val create_initial_vale_heap (ih:IB.interop_heap) : GTot vale_heap

val create_initial_vale_full_heap (ih:IB.interop_heap) (mt:memTaint_t) : Ghost vale_full_heap
  (requires True)
  (ensures fun h ->
    h == coerce (heap_create_impl ih mt) /\
    ME.mem_inv h /\
    ME.is_initial_heap h.vf_layout h.vf_heap /\
    ME.get_heaplet_id h.vf_heap == None /\
    h.vf_heap == create_initial_vale_heap ih
  )

unfold
let as_vale_stack (st:BS.machine_stack)
  : SI.vale_stack
  = IB.coerce st

val buffer_addr_is_nat64 (#t:base_typ) (x:ME.buffer t) (s:VS.vale_state)
  : Lemma (0 <= ME.buffer_addr x VS.(ME.get_vale_heap s.vs_heap) /\
           ME.buffer_addr x VS.(ME.get_vale_heap s.vs_heap) < pow2 64)

val code_equiv : squash (V.va_code == Vale.X64.Machine_Semantics_s.code)
val ins_equiv : squash (V.ins == Vale.X64.Machine_Semantics_s.ins)
val ocmp_equiv : squash (V.ocmp == Vale.X64.Machine_Semantics_s.ocmp)
