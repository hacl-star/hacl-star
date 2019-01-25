module Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module BV = LowStar.BufferView
module ME = X64.Memory
module VSig = Vale.AsLowStar.ValeSig

friend X64.Memory
friend X64.Memory_Sems
friend X64.Vale.Decls
friend X64.Vale.StateLemmas

let as_vale_buffer_len (#t:base_typ) (x:buf_t t)
   = BV.length_eq (BV.mk_buffer_view (as_vale_buffer x) (ME.uint_view t))

let state_eq_down_mem (va_s1:V.va_state) (s1:_) = ()

let rec loc_eq (args:list arg)
  : Lemma (VSig.mloc_modified_args args == loc_modified_args args)
  = match args with
    | [] -> ()
    | hd :: tl -> loc_eq tl

let relate_modifies (args:list arg) (m0 m1 : ME.mem) = loc_eq args
let reveal_readable (#t:_) (x:buf_t t) (s:ME.mem) = ()
let readable_live (#t:_) (x:buf_t t) (s:ME.mem) = ()
let buffer_readable_reveal #n bt x args h0 stack = ()
let get_heap_mk_mem_reveal #n args h0 stack = ()
let buffer_as_seq_reveal #n t x args h0 stack = ()
let buffer_as_seq_reveal2 t x va_s = ()
let buffer_addr_reveal t x args h0 = ()
let fuel_eq = ()
let decls_eval_code_reveal c va_s0 va_s1 f = ()
let as_vale_buffer_disjoint (#t1 #t2:base_typ) (x:buf_t t1) (y:buf_t t2) = ()

module IB=Interop.Base
module MS=X64.Machine_s
let valid_memtaint (mem:ME.mem) (ps:list b8{IB.list_disjoint_or_eq ps}) (ts:b8 -> GTot MS.taint)
  : Lemma (ME.valid_taint_bufs mem (IB.create_memtaint mem ps ts) ps ts)
  = ME.valid_memtaint mem ps ts
