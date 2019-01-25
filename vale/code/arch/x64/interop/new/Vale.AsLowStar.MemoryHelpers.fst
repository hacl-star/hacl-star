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

[@__reduce__]
let create_initial_vale_state
       (#n:IX64.max_slots)
       (args:IX64.arity_ok arg)
  : IX64.state_builder_t n args V.va_state =
  fun h0 stack ->
    let t_state, mem = IX64.create_initial_trusted_state n args I.down_mem h0 stack in
    let open VS in
    { ok = true;
      regs = X64.Vale.Regs.of_fun t_state.TS.state.BS.regs;
      xmms = X64.Vale.Xmms.of_fun t_state.TS.state.BS.xmms;
      flags = 0; // TODO: REVIEW
      mem = as_vale_mem mem;
      memTaint = TS.(t_state.memTaint) }

[@__reduce__]
let taint_hyp_arg (m:ME.mem) (tm:MS.memTaint_t) (a:arg) : prop =
   let (| tag, x |) = a in
    match tag with
    | TD_Buffer TUInt64 {taint=tnt} ->
      ME.valid_taint_buf64
         (as_vale_buffer #TUInt64 x)
         m
         tm
         tnt
      /\ True
    | TD_Buffer TUInt128 {taint=tnt} ->
      ME.valid_taint_buf64
         (as_vale_buffer #TUInt128 x)
         m
         tm
         tnt
      /\ True
    | _ ->
      True

[@__reduce__]
let taint_hyp (args:list arg) : VSig.sprop =
  fun s0 -> BigOps.big_and' (taint_hyp_arg s0.VS.mem s0.VS.memTaint) args

let taint_of_arg (a:arg) =
  let (| tag, x |) = a in
  match tag with
  | TD_Buffer TUInt64 {taint=tnt}
  | TD_Buffer TUInt128 {taint=tnt} -> Some tnt
  | _ -> None

let arg_b8 (a:arg{Some? (taint_of_arg a)}) : b8 =
  let (| tag, x |) = a in x

let rec args_b8_mem (args:list arg) (a:arg)
  : Lemma (List.memP a args /\ Some? (taint_of_arg a) ==> List.memP (arg_b8 a) (args_b8 args))
  = match args with
    | [] -> ()
    | hd::tl ->
      args_b8_mem tl a

let rec mk_taint_equiv
     (args:list arg{disjoint_or_eq args})
     (raw_taint:IX64.taint_map{raw_taint == IX64.(mk_taint args IX64.init_taint)})
     (a:arg)
   : Lemma (List.memP a args /\ Some? (taint_of_arg a) ==>
            Some?.v (taint_of_arg a) == raw_taint (arg_b8 a))
   = match args with
     | [] -> ()
     | hd::tl ->
       mk_taint_equiv tl IX64.(mk_taint tl init_taint) a;
       let (| tag, x |) = hd in
       match tag with
       | TD_Base _ -> ()
       | TD_Buffer _ {taint=tnt} ->
         disjoint_or_eq_cons hd tl;
         BigOps.big_and'_forall (disjoint_or_eq_1 hd) tl

let core_create_lemma_taint_hyp
    #n
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = create_initial_vale_state args h0 stack in
                taint_hyp args va_s /\
                ME.valid_taint_buf64 (as_vale_buffer stack) va_s.VS.mem va_s.VS.memTaint X64.Machine_s.Public))
  =
    let va_s = create_initial_vale_state args h0 stack in
    let taint_map = va_s.VS.memTaint in
    let s_args = arg_of_sb stack::args in
    let mem = va_s.VS.mem in
    assert (mem == mk_mem s_args h0);
    let raw_taint = IX64.(mk_taint s_args IX64.init_taint) in
    assert (taint_map == create_memtaint mem (args_b8 s_args) raw_taint);
    ME.valid_memtaint mem (args_b8 s_args) raw_taint;
    assert (forall x. List.memP x (args_b8 s_args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    assert (forall x. List.memP x (args_b8 args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    Classical.forall_intro (mk_taint_equiv s_args raw_taint);
    assert (forall (a:arg). List.memP a args /\ Some? (taint_of_arg a) ==> Some?.v (taint_of_arg a) == raw_taint (arg_b8 a));
    Classical.forall_intro (args_b8_mem args);
    assert (forall x. List.memP x args /\ Some? (taint_of_arg x) ==>
                 taint_hyp_arg mem taint_map x);
    BigOps.big_and'_forall (taint_hyp_arg mem taint_map) args

module IB=Interop.Base
module MS=X64.Machine_s
let valid_memtaint (mem:ME.mem) (ps:list b8{IB.list_disjoint_or_eq ps}) (ts:b8 -> GTot MS.taint)
  : Lemma (ME.valid_taint_bufs mem (IB.create_memtaint mem ps ts) ps ts)
  = ME.valid_memtaint mem ps ts
