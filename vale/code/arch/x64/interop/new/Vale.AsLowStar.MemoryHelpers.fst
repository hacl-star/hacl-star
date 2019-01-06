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

friend X64.Memory
friend X64.Memory_Sems

open Interop.Adapters

let down_mem_unify () : Lemma (IM.down_mem == Interop.down_mem) = 
  admit() // TODO: We should only have one def for down_mem

let mk_mem_reveal (args:list arg) (h0:mem_roots args) : Lemma
  (let mem = mk_mem args h0 in
   hs_of_mem mem == mem.ME.hs /\
   ptrs_of_mem mem == mem.ME.ptrs /\
   IA.addrs == mem.ME.addrs) =
   admit() // TODO: Will be provable with an implementation for Interop.Adapters

let buffer_readable_reveal bt x args h0 stack =
  let mem = mk_mem (arg_of_lb stack::args) h0 in
  mk_mem_injective (arg_of_lb stack::args) h0;
  mk_mem_reveal (arg_of_lb stack::args) h0

let get_heap_mk_mem_reveal args h0 stack =
  let mem = mk_mem (arg_of_lb stack::args) h0 in
  mk_mem_injective (arg_of_lb stack::args) h0;
  down_mem_unify ();
  mk_mem_reveal (arg_of_lb stack::args) h0

let buffer_as_seq_reveal t x args h0 stack =
  let y = as_vale_buffer x in
  let mem = mk_mem (arg_of_lb stack::args) h0 in
  assume (t <> ME.TUInt128); // TODO: TUInt128
  mk_mem_injective (arg_of_lb stack::args) h0;
  mk_mem_reveal (arg_of_lb stack::args) h0

let buffer_addr_reveal t x args h0 =
  mk_mem_reveal args h0
