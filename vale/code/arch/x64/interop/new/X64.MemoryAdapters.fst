module X64.MemoryAdapters

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module IB = Interop.Base
module VS = X64.Vale.State
friend X64.Memory
module T = FStar.Tactics
let buffer_eq = assert (ME.buffer == IB.buf_t) by (T.norm [delta_only [`%ME.buffer]]; T.trefl())
let mem_eq = ()
let buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.state) = ()

module V = X64.Vale.Decls
module TS = X64.Taint_Semantics_s
friend X64.Vale.Decls

let code_equiv : squash (V.va_code == TS.tainted_code) = ()
