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
let lemma_heap_impl = ()
let create_initial_vale_heap ih = (heap_create_impl ih (Map.const Secret)).vf_heap
let create_initial_vale_full_heap ih mt =
  let vfh = heap_create_impl ih mt in
  let vfh:(vfh:vale_full_heap{
    vfh.vf_heap.mh == (Map16.sel vfh.vf_heaplets 0).mh /\ 
    vfh.vf_heap.ih == (Map16.sel vfh.vf_heaplets 0).ih})
    =
    vfh
    in

  let h = vfh in
  let h1 = h.vf_heap in
  let h2 = (Map16.sel h.vf_heaplets 0) in
  assert (h1.mh == h2.mh);
  assert (h1.ih == h2.ih);
  assert (ME.mem_inv vfh);
  heap_create_impl ih mt

let buffer_addr_is_nat64 (#t:base_typ) (x:ME.buffer t) (s:VS.vale_state) = ()

module V = Vale.X64.Decls
friend Vale.X64.Decls

let code_equiv = ()
let ins_equiv = ()
let ocmp_equiv = ()
