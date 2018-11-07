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

let initial_vale_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc va_state

let create_initial_vale_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot va_state
  = let t_state, mem = create_initial_trusted_state_core acc regs xmms taint h0 stack in
    {ok = TS.(BS.(t_state.state.ok));
     regs = X64.Vale.Regs.of_fun TS.(BS.(t_state.state.regs));
     xmms =  X64.Vale.Xmms.of_fun TS.(BS.(t_state.state.xmms));
     flags = TS.(BS.(t_state.state.flags));
     mem = mem;
     memTaint = TS.(t_state.memTaint)}

let core_create_lemma
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : Lemma
      (ensures (fst (create_initial_trusted_state_core acc regs xmms taint h0 stack) ==
                state_to_S (create_initial_vale_state_core acc regs xmms taint h0 stack)))
  = let s_init, _ = create_initial_trusted_state_core acc regs xmms taint h0 stack in
    let s0 = create_initial_vale_state_core acc regs xmms taint h0 stack in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let create_vale_initial_state_t (dom:list vale_type)
                                (acc:list b8)
    = n_dep_arrow
          dom
          (initial_vale_state_t dom acc)


let elim_down_1 (hd:vale_type)
                (acc:list b8)
                (down:create_vale_initial_state_t [hd] acc)
                (x:vale_type_as_type hd)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::maybe_cons_buffer hd x acc)} -> GTot va_state =
    down x

let elim_down_nil (acc:list b8)
                  (down:create_vale_initial_state_t [] acc)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::acc)} -> GTot va_state =
    down

let elim_down_cons (hd:vale_type)
                   (tl:list vale_type)
                   (acc:list b8)
                   (down:create_vale_initial_state_t (hd::tl) acc)
                   (x:vale_type_as_type hd)
    : create_vale_initial_state_t tl (maybe_cons_buffer hd x acc) =
    elim_dep_arrow_cons hd tl down x

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
//vale_sig pre post: a template for a top-level signature provided by a vale function
//////////////////////////////////////////////////////////////////////////////////////////

let vale_pre_tl (dom:list vale_type) =
    n_arrow dom (va_state -> stack_buffer -> prop)

let vale_pre (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_pre_tl dom

let vale_post_tl (dom:list vale_type) =
    n_arrow dom
            (s0:va_state -> sb:stack_buffer -> s1:va_state -> f:va_fuel -> prop)

let vale_post (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_post_tl dom

let vale_save_reg (r:reg) (s0 s1:va_state) =
  eval_reg r s0 == eval_reg r s1

let rec vale_sig_tl (#dom:list vale_type)
                    (code:va_code)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) ->
                       eval_code code va_s0 f va_s1 /\
                       vale_save_reg Rbx va_s0 va_s1 /\
                       vale_save_reg Rsi va_s0 va_s1 /\
                       vale_save_reg Rdi va_s0 va_s1 /\
                       vale_save_reg Rbp va_s0 va_s1 /\
                       vale_save_reg Rsp va_s0 va_s1 /\
                       vale_save_reg R12 va_s0 va_s1 /\
                       vale_save_reg R13 va_s0 va_s1 /\
                       vale_save_reg R14 va_s0 va_s1 /\
                       vale_save_reg R15 va_s0 va_s1 /\
                       va_s1.ok /\
                       elim_nil post va_s0 stack_b va_s1 f))

    | hd::tl ->
      x:vale_type_as_type hd ->
      vale_sig_tl #tl code (elim_1 pre x) (elim_1 post x)

let elim_vale_sig_cons #code
                       (hd:vale_type)
                       (tl:list vale_type)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl code pre post)
    : x:vale_type_as_type hd
    -> vale_sig_tl code (elim_1 pre x) (elim_1 post x)
    = v

let vale_sig (#dom:list vale_type)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:va_code ->
    win:bool ->
    vale_sig_tl code (pre code win)
                     (post code win)

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////


let rec as_lowstar_sig_tl (#dom:list vale_type)
                          (code:va_code)
                          (acc:list b8)
                          (down:create_vale_initial_state_t dom acc)
                          (pre: vale_pre_tl dom)
                          (post: vale_post_tl dom)
    : Type =
    match dom with
    | [] ->
      unit ->
      Stack unit
        (requires (fun h0 ->
                    mem_roots_p h0 acc /\
                    (forall (push_h0:mem_roots acc)
                       (alloc_push_h0:mem_roots acc)
                       (b:stack_buffer).
                            HS.fresh_frame h0 push_h0 /\
                            M.modifies loc_none push_h0 alloc_push_h0 /\
                            HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
                            B.frameOf b == HS.get_tip alloc_push_h0 /\
                            B.live alloc_push_h0 b ==>
                            elim_nil pre (elim_down_nil acc down alloc_push_h0 b) b)))
        (ensures (fun h0 _ h1 ->
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
                            )))

    | hd::tl ->
      x:vale_type_as_type hd ->
      as_lowstar_sig_tl
        #tl
        code
        (maybe_cons_buffer hd x acc)
        (elim_down_cons hd tl acc down x)
        (elim_1 pre x)
        (elim_1 post x)

let create_vale_initial_state
      (is_win:bool)
      (dom:list vale_type{List.length dom < max_arity is_win})
    : create_vale_initial_state_t dom []
    = create_initial_state_aux
          dom
          is_win
          0
          init_regs
          init_xmms
          []
          init_taint
          create_initial_vale_state_core

let as_lowstar_sig  (c:code) (dom:list vale_type{List.length dom < max_arity win})
                    (pre: vale_pre dom)
                    (post: vale_post dom) =
    as_lowstar_sig_tl
      #dom
      c
      []
      (create_vale_initial_state win dom)
      (pre c win)
      (post c win)

////////////////////////////////////////////////////////////////////////////////

let elim_vale_sig_nil  #code
                       (pre:vale_pre_tl [])
                       (post:vale_post_tl [])
                       (v:vale_sig_tl code pre post)
    : va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) -> elim_nil post va_s0 stack_b va_s1 f))
    = v

let elim_trusted_lowstar_sig_nil
      #code
      (acc:list b8)
      (down:create_trusted_initial_state_t [] acc)
      (v:IS.as_lowstar_sig_tl code [] acc down)
    : h0:HS.mem ->
      predict:prediction code acc down h0 ->
      Stack (as_lowstar_sig_ret acc)
        (requires (fun h0' -> h0 == h0' /\ mem_roots_p h0 acc /\ True))
        (ensures (fun h0 (As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem) h1 ->
          IS.as_lowstar_sig_post code acc down h0 predict push_h0 alloc_push_h0 b fuel final_mem h1))
    = v

let elim_trusted_lowstar_sig_cons
      #code
      (hd:vale_type)
      (tl:list vale_type)
      (acc:list b8)
      (down:create_trusted_initial_state_t (hd::tl) acc)
      (v:IS.as_lowstar_sig_tl code (hd::tl) acc down)
    : x:vale_type_as_type hd ->
      IS.as_lowstar_sig_tl
        code
        tl
        (maybe_cons_buffer hd x acc)
        (IS.elim_down_cons hd tl acc down x)
    = v

let rec wrap_tl
         #code
         (dom:list vale_type)
         (acc:list b8)
         (v_down:create_vale_initial_state_t dom acc)
         (t_down:create_trusted_initial_state_t dom acc{n_dep_arrow_equiv dom acc t_down v_down})
         (pre:vale_pre_tl dom)
         (post:vale_post_tl dom)
         (v:vale_sig_tl code pre post)
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
                (requires
                  HS.fresh_frame h0 push_h0 /\
                  M.modifies loc_none push_h0 alloc_push_h0 /\
                  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
                  B.frameOf b == HS.get_tip alloc_push_h0 /\
                  B.live alloc_push_h0 b /\
                  s0 == fst (IS.elim_down_nil acc t_down alloc_push_h0 b)
                )
                (ensures fun (fuel, final_mem) ->
                  Some? (TS.taint_eval_code code fuel s0) /\ (
                    let sN = Some?.v (TS.taint_eval_code code fuel s0) in
                    Interop.down_mem final_mem.hs final_mem.addrs final_mem.ptrs == sN.TS.state.BS.mem /\
                    save_reg Rbx s0 sN /\
                    save_reg Rsi s0 sN /\
                    save_reg Rdi s0 sN /\
                    save_reg Rbp s0 sN /\
                    save_reg Rsp s0 sN /\
                    save_reg R12 s0 sN /\
                    save_reg R13 s0 sN /\
                    save_reg R14 s0 sN /\
                    save_reg R15 s0 sN /\
                    sN.TS.state.BS.ok
                  )
                )
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
           let acc' = maybe_cons_buffer hd x acc in
           let t_down' : create_trusted_initial_state_t tl acc' = IS.elim_down_cons hd tl acc t_down x in
           wrap_tl tl
                  acc'
                  (elim_down_cons hd tl acc v_down x)
                  (IS.elim_down_cons hd tl acc t_down x)
                  (elim_1 pre x)
                  (elim_1 post x)
                  (elim_vale_sig_cons hd tl pre post v x)
                  (elim_trusted_lowstar_sig_cons hd tl acc t_down t_low x)
        in
        f


let wrap #code
         (dom:list vale_type{List.length dom < max_arity win})
         (pre:vale_pre dom)
         (post:vale_post dom)
         (v:vale_sig pre post)
         (t_low:IS.as_lowstar_sig code dom)
  : as_lowstar_sig code dom pre post =
  equiv_create_trusted_and_vale_state dom 0 init_regs init_xmms [] init_taint;
  wrap_tl
    dom
    []
    (create_vale_initial_state win dom)
    (create_trusted_initial_state win dom)
    (pre code win)
    (post code win)
    (v code win)
    t_low

////////////////////////////////////////////////////////////////////////////////
//test
////////////////////////////////////////////////////////////////////////////////
open Vale_memcpy
let lem_memcpy (va_b0:va_code)
               (win:bool)
               (dst:buffer64)
               (src:buffer64)
               (va_s0:va_state)
               (stack_b:buffer64)
  :  Ghost (va_state & va_fuel)
           (requires va_pre va_b0 va_s0 win stack_b dst src )
           (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b dst src )) =
   Vale_memcpy.va_lemma_memcpy va_b0 va_s0 win stack_b dst src

(*
unfold
let dom : l:list vale_type{List.Tot.length l < max_arity win} =
  let d = [VT_Buffer TUInt64; VT_Buffer TUInt64;] in
  assert_norm (List.Tot.length d < max_arity win);
  d

let pre : vale_pre dom =
  fun (va_b0:code)
    (win:bool)
    (dst:buffer64)
    (src:buffer64)
    (va_s0:va_state)
    (stack_b:buffer64) -> va_pre va_b0 va_s0 win stack_b dst src

let post : vale_post dom =
  fun (va_b0:code)
    (win:bool)
    (dst:buffer64)
    (src:buffer64)
    (va_s0:va_state)
    (stack_b:buffer64)
    (va_sM:va_state)
    (va_fM:fuel) -> va_post va_b0 va_s0 va_sM va_fM win stack_b dst src

let memcpy_raw
    : as_lowstar_sig pre post
    = wrap [VT_Buffer TUInt64; VT_Buffer TUInt64;] pre post lem_memcpy

unfold let norm (#a:Type) (x:a) : a = normalize_term x

let force (#a:Type) (x:a) : norm a = x

let elim_lowstar_sig (#dom:list vale_type{List.length dom < max_arity win})
                     (#pre:vale_pre dom)
                     (#post:vale_post dom)
                     (f:as_lowstar_sig pre post)
    : norm (as_lowstar_sig pre post)
    = force f

let pre_cond (h:HS.mem) (dst:b8) (src:b8) = live h dst /\ live h src /\ bufs_disjoint [dst;src] /\ length dst % 8 == 0 /\ length src % 8 == 0 /\ length dst == 16 /\ length src == 16

let post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8) =
  live h dst /\ live h src /\
  live h' dst /\ live h' src /\
  length dst % 8 == 0 /\ length src % 8 == 0 /\
  (let dst_b = BV.mk_buffer_view dst Views.view64 in
  let src_b = BV.mk_buffer_view src Views.view64 in
  Seq.equal (BV.as_seq h' dst_b) (BV.as_seq h' src_b))

let full_post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8)  =
  post_cond h h' dst src  /\
  M.modifies (M.loc_buffer dst) h h'

val memcpy: dst:buffer64 -> src:buffer64 -> Stack unit
        (requires (fun h -> pre_cond h dst src ))
        (ensures (fun h0 _ h1 -> full_post_cond h0 h1 dst src ))
let memcpy dst src =
  assume false; //TODO
  elim_lowstar_sig memcpy_raw (Vale_memcpy.va_code_memcpy win) dst src ()

////////////////////////////////////////////////////////////////////////////////
*)
