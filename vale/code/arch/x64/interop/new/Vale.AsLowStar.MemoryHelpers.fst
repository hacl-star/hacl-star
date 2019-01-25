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
let modifies_same_roots s h0 h1 = ()
let modifies_equal_domains s h0 h1 = ()

let core_create_lemma_taint_hyp
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state args h0 stack in
                LSig.taint_hyp args va_s /\
                ME.valid_taint_buf64 (as_vale_buffer stack) va_s.VS.mem va_s.VS.memTaint X64.Machine_s.Public))
  = let va_s = LSig.create_initial_vale_state args h0 stack in
    let taint_map = va_s.VS.memTaint in
    let s_args = arg_of_sb stack::args in
    let mem = va_s.VS.mem in
    assert (mem == mk_mem s_args h0);
    let raw_taint = IX64.(mk_taint s_args IX64.init_taint) in
    assert (taint_map == create_memtaint mem (args_b8 s_args) raw_taint);
    ME.valid_memtaint mem (args_b8 s_args) raw_taint;
    assert (forall x. List.memP x (args_b8 s_args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    assert (forall x. List.memP x (args_b8 args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    Classical.forall_intro (IX64.mk_taint_equiv s_args);
    assert (forall (a:arg). List.memP a args /\ Some? (IX64.taint_of_arg a) ==>
            Some?.v (IX64.taint_of_arg a) == raw_taint (IX64.taint_arg_b8 a));
    Classical.forall_intro (args_b8_mem args);
    assert (forall x. List.memP x args /\ Some? (IX64.taint_of_arg x) ==>
                 LSig.taint_hyp_arg mem taint_map x);
    BigOps.big_and'_forall (LSig.taint_hyp_arg mem taint_map) args
