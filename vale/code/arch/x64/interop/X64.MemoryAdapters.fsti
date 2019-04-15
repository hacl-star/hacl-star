module X64.MemoryAdapters

open Interop.Base
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module SI = X64.Stack_i
module IB = Interop.Base
module VS = X64.Vale.State
module V = X64.Vale.Decls
module TS = X64.Taint_Semantics_s

val as_vale_buffer (#src #t:_) (i:IB.buf_t src t) : GTot (ME.buffer t)
val as_vale_immbuffer (#src #t:_) (i:IB.ibuf_t src t) : GTot (ME.buffer t)

val mem_eq : squash (ME.mem == IB.mem)
val stack_eq : squash (BS.stack == SI.stack)

unfold
let as_mem (m:ME.mem)
  : IB.mem
  = IB.coerce m

unfold
let as_vale_mem (m:IB.mem)
  : ME.mem
  = IB.coerce m

unfold
let as_vale_stack (st:BS.stack)
  : SI.stack
  = IB.coerce st

val buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.state)
  : Lemma (0 <= ME.buffer_addr x VS.(s.mem) /\
           ME.buffer_addr x VS.(s.mem) < pow2 64)

val code_equiv : squash (V.va_code == TS.tainted_code)
val ins_equiv : squash (V.ins == TS.tainted_ins)
val ocmp_equiv : squash (V.ocmp == TS.tainted_ocmp)
