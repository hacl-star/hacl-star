module Vale.AsLowStar.Wrapper
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module LU = LowStar.Util
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
// open Vale.AsLowStar.Signature
// open Vale.AsLowStar.Util
// friend X64.Interop_s
// friend X64.Memory
// friend X64.Vale.Decls
// friend X64.Vale.StateLemmas
// friend X64.Memory_Sems
// module B = LowStar.Buffer
// module BV = LowStar.BufferView
// module HS = FStar.HyperStack
// module IA = Interop_assumptions
// module IS = X64.Interop_s
// module ME = X64.Memory
// module MS = X64.Machine_s
// module V = X64.Vale.Decls
// module VS = X64.Vale.State
// module VSig = Vale.AsLowStar.ValeSig
// module LSig = Vale.AsLowStar.LowStarSig
// module TS = X64.Taint_Semantics_s
module SL = X64.Vale.StateLemmas
// module BS = X64.Bytes_Semantics_s
// module MS = X64.Memory_Sems


[@reduce]
let create_initial_vale_state
       (args:IX64.arity_ok arg)
  : IX64.state_builder_t args V.va_state =
  fun h0 stack ->
    let t_state, mem = IX64.create_initial_trusted_state args h0 stack in
    let open VS in
    { ok = true;
      regs = X64.Vale.Regs.of_fun t_state.TS.state.BS.regs;
      xmms = X64.Vale.Xmms.of_fun t_state.TS.state.BS.xmms;
      flags = 0; // REVIEW
      mem = mem;
      memTaint = TS.(t_state.memTaint) }

let lemma_create_initial_vale_state_core
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IM.b8{mem_roots_p h0 (IX64.arg_of_b8 stack::args)})
  : Lemma
      (ensures (
        let s = create_initial_vale_state args h0 stack in
        Interop.Adapters.hs_of_mem VS.(s.mem) == h0
      ))
  = Interop.Adapters.mk_mem_injective (IX64.arg_of_b8 stack::args) h0

let core_create_lemma
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:b8{mem_roots_p h0 (IX64.arg_of_b8 stack::args)})
  : Lemma
      (ensures (fst (IX64.create_initial_trusted_state args h0 stack) ==
                SL.state_to_S (create_initial_vale_state args h0 stack)))
  = admit() //needs the definition of SL.state_to_S; not sure why its hidden in StateLemma
module ST = FStar.HyperStack.ST

let code_equiv : squash (V.va_code == TS.tainted_code) = admit()

let rec wrap_aux
         (code:V.va_code)
         (dom:list td)
         (args:list arg{List.length args + List.length dom < IX64.max_arity})
         (num_stack_slots:nat)
         (pre:VSig.vale_pre_tl dom)
         (post:VSig.vale_post_tl dom)
         (v:VSig.vale_sig_tl args code pre post)
    : LSig.as_lowstar_sig_tl args num_stack_slots pre post
    = match dom with
      | [] ->
        let code : TS.tainted_code = coerce code in
        let f : LSig.as_lowstar_sig_tl #[] args num_stack_slots pre post =
          fun () ->
            let h0 = ST.get () in
            let f_predict
                (s0:TS.traceState)
                (push_h0:mem_roots args)
                (alloc_push_h0:mem_roots args)
                (b:IX64.stack_buffer{mem_roots_p alloc_push_h0 (IX64.arg_of_b8 b::args)})
              : Ghost (nat & ME.mem)
                  (requires IX64.prediction_pre code args h0 s0 push_h0 alloc_push_h0 b)
                  (ensures IX64.prediction_post code args h0 s0 push_h0 alloc_push_h0 b)
                = admit()
                // let va_s0 = elim_down_nil acc v_down alloc_push_h0 b in
                // let va_s1, fuel = elim_vale_sig_nil pre post v va_s0 (to_b8 b) in
                // (fuel, va_s1.mem)
            in
            let predict : IX64.prediction code args h0 = f_predict in
            let IX64.As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem =
              IX64.wrap code args h0 predict
            in
            admit()
            // let h1 = get () in
            // assert (
            //   let initial_state = elim_down_nil acc v_down alloc_push_h0 b in
            //   let (final, fuel) = elim_vale_sig_nil pre post v initial_state b in
            //   eval_code code initial_state fuel final
            // );
            // ()
        in
        f <: LSig.as_lowstar_sig_tl #[] args num_stack_slots pre post
      | hd::tl ->
        let f (x:td_as_type hd) =
          wrap_aux
              code
              tl
              ((|hd,x|)::args)
              num_stack_slots
              (elim_1 pre x)
              (elim_1 post x)
              (VSig.elim_vale_sig_cons hd tl args pre post v x)
        in
        f


let wrap
    (code:V.va_code)
    (dom:IX64.arity_ok td)
    (num_stack_slots:nat)
    (pre:VSig.vale_pre dom)
    (post:VSig.vale_post dom)
    (v:VSig.vale_sig pre post)
  : LSig.as_lowstar_sig code dom num_stack_slots pre post
  = wrap_aux code dom [] num_stack_slots (pre code) (post code) (v code IA.win)
