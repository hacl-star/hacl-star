module Vale.X64.MemoryAdapters

open FStar.Mul
open Vale.Interop.Base
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module IB = Vale.Interop.Base
module VS = Vale.X64.State
module T = FStar.Tactics
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
open Vale.Arch.HeapImpl
open Vale.Arch.Heap

friend Vale.Arch.HeapImpl
friend Vale.Arch.Heap
friend Vale.X64.Memory
friend Vale.X64.Stack_i

let as_vale_buffer #src #t i =
  DV.length_eq (get_downview i);
  IB.mut_to_b8 src i

let as_vale_immbuffer #src #t i =
  DV.length_eq (get_downview i);
  IB.imm_to_b8 src i

let mem_eq = ()
let stack_eq = ()

let as_mem h = _ih h
let as_vale_mem ih = heap_of_interop ih

let buffer_addr_is_nat64 (#t:_) (x:ME.buffer t) (s:VS.vale_state) = ()

module V = Vale.X64.Decls
friend Vale.X64.Decls

let code_equiv = ()
let ins_equiv = ()
let ocmp_equiv = ()
