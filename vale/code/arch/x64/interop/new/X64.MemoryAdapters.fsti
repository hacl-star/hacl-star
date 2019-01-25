module X64.MemoryAdapters

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module IB = Interop.Base

val buffer_eq : squash (ME.buffer == IB.buf_t)
unfold
let as_vale_buffer (#t:_) (i:IB.buf_t t) : ME.buffer t = IB.coerce i
unfold
let as_lowstar_buffer (#t:_) (i:ME.buffer t) : IB.buf_t t = IB.coerce i

val mem_eq : squash (ME.mem == IB.mem)
unfold
let as_mem (m:ME.mem) : IB.mem = IB.coerce m
unfold
let as_vale_mem (m:IB.mem) : ME.mem = IB.coerce m
