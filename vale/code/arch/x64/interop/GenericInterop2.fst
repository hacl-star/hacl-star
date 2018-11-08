module GenericInterop2

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
open X64.Vale.StateLemmas
open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory_s
module BS = X64.Bytes_Semantics_s
module IS = X64.Interop_s
open X64.Interop_s

friend X64.Interop_s
friend X64.Memory_s
friend X64.Memory
friend X64.Vale.Decls
friend X64.Vale.StateLemmas

let create_initial_vale_state_core acc regs xmms taint h0 stack =
    let t_state, mem = create_initial_trusted_state_core acc regs xmms taint h0 stack in
    {ok = TS.(BS.(t_state.state.ok));
     regs = X64.Vale.Regs.of_fun TS.(BS.(t_state.state.regs));
     xmms =  X64.Vale.Xmms.of_fun TS.(BS.(t_state.state.xmms));
     flags = TS.(BS.(t_state.state.flags));
     mem = mem;
     memTaint = TS.(t_state.memTaint)}

let core_create_lemma acc regs xmms taint h0 stack =
    let s_init, _ = create_initial_trusted_state_core acc regs xmms taint h0 stack in
    let s0 = create_initial_vale_state_core acc regs xmms taint h0 stack in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let rec n_dep_arrow_equiv (dom:list vale_type)
                          (acc:list b8)
                          (f:create_trusted_initial_state_t dom acc)
                          (g:create_vale_initial_state_t dom acc) =
    match dom with
    | [] ->
      forall h0 (stack:b8{mem_roots_p h0 (stack::acc)}).
        fst (IS.elim_down_nil acc f h0 stack) == state_to_S (elim_down_nil acc g h0 stack)

    | hd::tl ->
      forall (x:vale_type_as_type hd).
        n_dep_arrow_equiv tl (maybe_cons_buffer hd x acc)
                             (IS.elim_down_cons hd tl acc f x)
                             (elim_down_cons hd tl acc g x)

let rec equiv_create_trusted_and_vale_state
          (dom:list vale_type)
          (i:nat{i + List.length dom < max_arity win})
          (regs:_)
          (xmms:_)
          (acc:list b8)
          (taint:_)
    : Lemma (n_dep_arrow_equiv
                  dom
                  acc
                  (create_initial_state_aux dom win i regs xmms acc taint
                                                         create_initial_trusted_state_core)
                  (create_initial_state_aux dom win i regs xmms acc taint
                                                         create_initial_vale_state_core))
     = match dom with
       | [] ->
         FStar.Classical.forall_intro_2 (core_create_lemma acc regs xmms taint)
       | hd::tl ->
         let aux (x:vale_type_as_type hd)
           : Lemma (n_dep_arrow_equiv
                      tl
                      (maybe_cons_buffer hd x acc)
                      (create_initial_state_aux tl win (i + 1) (update_regs x win i regs) xmms (maybe_cons_buffer hd x acc) (update_taint_map x taint) create_initial_trusted_state_core)
                      (create_initial_state_aux tl win (i + 1) (update_regs x win i regs) xmms (maybe_cons_buffer hd x acc) (update_taint_map x taint) create_initial_vale_state_core))
         =
           equiv_create_trusted_and_vale_state
                tl
                (i + 1)
                (update_regs x win i regs)
                xmms
                (maybe_cons_buffer hd x acc)
                (update_taint_map x taint)
          in
          FStar.Classical.forall_intro aux

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////

let as_lowstar_sig_tl_req code acc down pre post h0 =
                    mem_roots_p h0 acc /\
                    (forall (push_h0:mem_roots acc)
                       (alloc_push_h0:mem_roots acc)
                       (b:stack_buffer).
                            HS.fresh_frame h0 push_h0 /\
                            M.modifies loc_none push_h0 alloc_push_h0 /\
                            HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
                            B.frameOf b == HS.get_tip alloc_push_h0 /\
                            B.live alloc_push_h0 b ==>
                            elim_nil pre (elim_down_nil acc down alloc_push_h0 b) b)

let as_lowstar_sig_tl_ens code acc down pre post h0 _ h1 =
                       exists push_h0 alloc_push_h0 b final fuel.//  {:pattern
                                 // (post push_h0 alloc_push_h0 b final fuel)}
                            HS.fresh_frame h0 push_h0 /\
                            M.modifies loc_none push_h0 alloc_push_h0 /\
                            HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
                            B.frameOf b == HS.get_tip alloc_push_h0 /\
                            B.live alloc_push_h0 b /\
                            (let initial_state =
                                 elim_down_nil acc down alloc_push_h0 b in
                             elim_nil
                              post
                              initial_state
                              b
                              final
                              fuel /\
                            eval_code code initial_state fuel final /\
                            HS.poppable final.mem.hs /\
                            h1 == HS.pop (final.mem.hs)
                            )

////////////////////////////////////////////////////////////////////////////////

#reset-options "--z3rlimit 50"

let rec wrap_tl
         (code:code)
         (dom:list vale_type)
         (acc:list b8)
         (v_down:create_vale_initial_state_t dom acc)
         (t_down:create_trusted_initial_state_t dom acc{n_dep_arrow_equiv dom acc t_down v_down})
         (pre:vale_pre_tl dom)
         (post:vale_post_tl dom)
         (v:vale_sig_tl code win pre post)
         (t_low:IS.as_lowstar_sig_tl code dom acc t_down)
    : as_lowstar_sig_tl code acc v_down pre post
    = match dom with
      | [] ->
        let f : as_lowstar_sig_tl #[] code acc v_down pre post =
          fun () ->
            let h0 = get () in
            let f_predict
                (s0:TS.traceState)
                (push_h0:mem_roots acc)
                (alloc_push_h0:mem_roots acc)
                (b:stack_buffer{mem_roots_p alloc_push_h0 (b::acc)})
              : Ghost (nat & mem)
                  (requires prediction_pre code acc t_down h0 s0 push_h0 alloc_push_h0 b)
                  (ensures prediction_post code acc t_down h0 s0 push_h0 alloc_push_h0 b)
                =
                let va_s0 = elim_down_nil acc v_down alloc_push_h0 b in
                let va_s1, fuel = elim_vale_sig_nil pre post v va_s0 b in
                (fuel, va_s1.mem)
            in
            let predict : prediction code acc t_down h0 = f_predict in
            let As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem =
              elim_trusted_lowstar_sig_nil acc t_down t_low h0 predict in
            let h1 = get () in
            assert (
              let initial_state = elim_down_nil acc v_down alloc_push_h0 b in
              let (final, fuel) = elim_vale_sig_nil pre post v initial_state b in
              eval_code code initial_state fuel final
            );
            ()
        in
        f <: as_lowstar_sig_tl #[] code acc v_down pre post
      | hd::tl ->
        let f (x:vale_type_as_type hd)
           : as_lowstar_sig_tl code
                               (maybe_cons_buffer hd x acc)
                               (elim_down_cons hd tl acc v_down x)
                               (elim_1 pre x)
                               (elim_1 post x)
           =
           wrap_tl code tl
                  (maybe_cons_buffer hd x acc)
                  (elim_down_cons hd tl acc v_down x)
                  (IS.elim_down_cons hd tl acc t_down x)
                  (elim_1 pre x)
                  (elim_1 post x)
                  (elim_vale_sig_cons hd tl pre post v x)
                  (elim_trusted_lowstar_sig_cons hd tl acc t_down t_low x)
        in
        f

let lower_code c = c

let wrap code dom pre post v t_low =
  equiv_create_trusted_and_vale_state dom 0 init_regs init_xmms [] init_taint;
  fun () ->
    wrap_tl
      code
      dom
      []
      (create_vale_initial_state win dom)
      (create_trusted_initial_state win dom)
      (pre code win)
      (post code win)
      (v code win)
      t_low

