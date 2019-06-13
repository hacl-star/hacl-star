module Vale.X64.MemoryAdapters

open Vale.Interop.Base
module BS = Vale.X64.Machine_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module SI = Vale.X64.Stack_i
module IB = Vale.Interop.Base
module VS = Vale.X64.State
module V = Vale.X64.Decls
val as_vale_buffer (#src #t:_) (i:IB.buf_t src t) : GTot (ME.buffer t)
val as_vale_immbuffer (#src #t:_) (i:IB.ibuf_t src t) : GTot (ME.buffer t)

val mem_eq : squash (ME.vale_heap == IB.interop_heap)
val stack_eq : squash (BS.machine_stack == SI.vale_stack)

unfold
let as_mem (m:ME.vale_heap)
  : IB.interop_heap
  = IB.coerce m

unfold
let as_vale_mem (m:IB.interop_heap)
  : ME.vale_heap
  = IB.coerce m

unfold
let as_vale_stack (st:BS.machine_stack)
  : SI.vale_stack
  = IB.coerce st

val buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.vale_state)
  : Lemma (0 <= ME.buffer_addr x VS.(s.vs_heap) /\
           ME.buffer_addr x VS.(s.vs_heap) < pow2 64)

val code_equiv : squash (V.va_code == Vale.X64.Machine_Semantics_s.code)
val ins_equiv : squash (V.ins == Vale.X64.Machine_Semantics_s.ins)
val ocmp_equiv : squash (V.ocmp == Vale.X64.Machine_Semantics_s.ocmp)
