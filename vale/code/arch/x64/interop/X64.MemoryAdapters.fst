module X64.MemoryAdapters

open Interop.Base
module HS = FStar.HyperStack
module ME = X64.Memory
module IB = Interop.Base
module VS = X64.Vale.State
module T = FStar.Tactics
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down

friend X64.Memory
friend X64.Stack_i

let as_vale_buffer #src #t i = 
  DV.length_eq (get_downview i);
  IB.mut_to_b8 src i

let as_vale_immbuffer #src #t i = 
  DV.length_eq (get_downview i);
  IB.imm_to_b8 src i

let mem_eq = ()
let stack_eq = ()
let buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.state) = ()

module V = X64.Vale.Decls
module TS = X64.Taint_Semantics_s
friend X64.Vale.Decls

let code_equiv : squash (V.va_code == TS.tainted_code) = ()
let ins_equiv : squash (V.ins == TS.tainted_ins) = ()
let ocmp_equiv : squash (V.ocmp == TS.tainted_ocmp) = ()
