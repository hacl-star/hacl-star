module X64.MemoryAdapters

open Interop.Base
module HS = FStar.HyperStack
module ME = X64.Memory
module IB = Interop.Base
module VS = X64.Vale.State
friend X64.Memory
module T = FStar.Tactics
module B = LowStar.Buffer

let as_vale_buffer #t i = IB.Buffer (i <: B.buffer UInt8.t) true

let mem_eq = ()
let buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.state) = ()

module V = X64.Vale.Decls
module TS = X64.Taint_Semantics_s
friend X64.Vale.Decls

let code_equiv : squash (V.va_code == TS.tainted_code) = ()
