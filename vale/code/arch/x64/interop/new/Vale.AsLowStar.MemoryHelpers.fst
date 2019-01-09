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
friend X64.Vale.Decls
friend X64.Vale.StateLemmas
open Interop.Adapters

let down_mem_unify () : Lemma (IM.down_mem == Interop.down_mem) = 
  admit() // TODO: We should only have one def for down_mem

let mem_reveal (mem:ME.mem) : Lemma 
  (hs_of_mem mem == mem.ME.hs /\ ptrs_of_mem mem == mem.ME.ptrs)
  = admit() // TODO: Will be provable with an implementation for Interop.Adapters

let state_eq_down_mem (va_s1:V.va_state) (s1:_)
  = down_mem_unify();
    mem_reveal va_s1.VS.mem;
    assume (va_s1.VS.mem.ME.addrs == IA.addrs) //TODO: Needs a stronger invariant on mem.addrs

let rec loc_eq (args:list arg)
  : Lemma (VSig.mloc_modified_args args == loc_modified_args args)
  = match args with
    | [] -> ()
    | hd :: tl -> loc_eq tl

let relate_modifies (args:list arg) (m0 m1 : ME.mem)
  = loc_eq args;
    mem_reveal m0;
    mem_reveal m1

let mk_mem_addrs_reveal (args:list arg) (h0:mem_roots args) : Lemma
  (let mem = mk_mem args h0 in
   IA.addrs == mem.ME.addrs) =
   admit() // TODO: Will be provable with an implementation for Interop.Adapters

let reveal_readable (#t:_) (x:lowstar_buffer t) (s:ME.mem)
  = mem_reveal s

let readable_live (#t:_) (x:lowstar_buffer t) (s:ME.mem)
  = mem_reveal s

let buffer_readable_reveal bt x args h0 stack =
  let mem = mk_mem (arg_of_lb stack::args) h0 in
  mk_mem_injective (arg_of_lb stack::args) h0;
  mem_reveal mem

let get_heap_mk_mem_reveal args h0 stack =
  mk_mem_injective (arg_of_lb stack::args) h0;
  down_mem_unify ();
  mk_mem_addrs_reveal (arg_of_lb stack::args) h0;
  mem_reveal (mk_mem (arg_of_lb stack::args) h0)

let buffer_as_seq_reveal t x args h0 stack =
  assume (t <> ME.TUInt128); // TODO: TUInt128
  mk_mem_injective (arg_of_lb stack::args) h0;
  mem_reveal (mk_mem (arg_of_lb stack::args) h0)
  
let buffer_as_seq_reveal2 t x va_s =
  assume (t <> ME.TUInt128); // TODO: TUInt128
  let mem = va_s.VS.mem in
  mem_reveal mem
  
let buffer_addr_reveal t x args h0 =
  mk_mem_addrs_reveal args h0;
  mem_reveal (mk_mem args h0)

let fuel_eq = ()

let decls_eval_code_reveal c va_s0 va_s1 f = ()
