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
module MM = X64.Memory
open X64.Interop_s

val get_hs (m:X64.Memory.mem) : HS.mem
val to_mem (m:ME.mem) : m':MM.mem{m === m'}
val to_memtaint (m:X64.Machine_s.memTaint_t) : m':MM.memtaint{m === m'}

[@reduce]
let initial_vale_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc va_state

[@reduce]
let create_initial_vale_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot va_state =
  let t_state, mem = create_initial_trusted_state_core acc regs xmms taint h0 stack in
  { ok = TS.(BS.(t_state.state.ok));
    regs = X64.Vale.Regs.of_fun TS.(BS.(t_state.state.regs));
    xmms =  X64.Vale.Xmms.of_fun TS.(BS.(t_state.state.xmms));
    flags = TS.(BS.(t_state.state.flags));
    mem = to_mem mem;
    memTaint = to_memtaint TS.(t_state.memTaint) }

val core_create_lemma
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : Lemma
      (ensures (fst (create_initial_trusted_state_core acc regs xmms taint h0 stack) ==
                state_to_S (create_initial_vale_state_core acc regs xmms taint h0 stack)))

[@reduce]
let create_vale_initial_state_t (dom:list vale_type)
                                (acc:list b8)
    = n_dep_arrow
          dom
          (initial_vale_state_t dom acc)


[@reduce]
let elim_down_1 (hd:vale_type)
                (acc:list b8)
                (down:create_vale_initial_state_t [hd] acc)
                (x:vale_type_as_type hd)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::maybe_cons_buffer hd x acc)} -> GTot va_state =
    down x

[@reduce]
let elim_down_nil (acc:list b8)
                  (down:create_vale_initial_state_t [] acc)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::acc)} -> GTot va_state =
    down

[@reduce]
let elim_down_cons (hd:vale_type)
                   (tl:list vale_type)
                   (acc:list b8)
                   (down:create_vale_initial_state_t (hd::tl) acc)
                   (x:vale_type_as_type hd)
    : create_vale_initial_state_t tl (maybe_cons_buffer hd x acc) =
    elim_dep_arrow_cons hd tl down x

//////////////////////////////////////////////////////////////////////////////////////////
//vale_sig pre post: a template for a top-level signature provided by a vale function
//////////////////////////////////////////////////////////////////////////////////////////

[@reduce]
let vale_pre_tl (dom:list vale_type) =
    n_arrow dom (va_state -> stack_buffer -> prop)

[@reduce]
let vale_pre (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_pre_tl dom

[@reduce]
let vale_post_tl (dom:list vale_type) =
    n_arrow dom
            (s0:va_state -> sb:stack_buffer -> s1:va_state -> f:va_fuel -> prop)

[@reduce]
let vale_post (dom:list vale_type) =
    code:va_code ->
    win:bool ->
    vale_post_tl dom

let vale_save_reg (r:reg) (s0 s1:va_state) =
  eval_reg r s0 == eval_reg r s1

let vale_save_xmm (r:xmm) (s0 s1:va_state) =
  eval_xmm r s0 == eval_xmm r s1

let vale_calling_conventions (win:bool) (s0 s1:va_state) =
  vale_save_reg Rbx s0 s1 /\
  (win ==> vale_save_reg Rsi s0 s1) /\
  (win ==> vale_save_reg Rdi s0 s1) /\
  vale_save_reg Rbp s0 s1 /\
  (win ==> vale_save_reg Rsp s0 s1) /\ // TODO: also needed for !win
  vale_save_reg R12 s0 s1 /\
  vale_save_reg R13 s0 s1 /\
  vale_save_reg R14 s0 s1 /\
  vale_save_reg R15 s0 s1 /\
  (win ==>
    vale_save_xmm 6 s0 s1 /\
    vale_save_xmm 7 s0 s1 /\
    vale_save_xmm 8 s0 s1 /\
    vale_save_xmm 9 s0 s1 /\
    vale_save_xmm 10 s0 s1 /\
    vale_save_xmm 11 s0 s1 /\
    vale_save_xmm 12 s0 s1 /\
    vale_save_xmm 13 s0 s1 /\
    vale_save_xmm 14 s0 s1 /\
    vale_save_xmm 15 s0 s1
  ) /\
  s1.ok

[@reduce]
let rec vale_sig_tl (#dom:list vale_type)
                    (code:va_code)
                    (win:bool)
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
                       X64.Vale.Decls.eval_code code va_s0 f va_s1 /\
                       vale_calling_conventions win va_s0 va_s1 /\
                       elim_nil post va_s0 stack_b va_s1 f))

    | hd::tl ->
      x:vale_type_as_type hd ->
      vale_sig_tl #tl code win (elim_1 pre x) (elim_1 post x)

[@reduce]
let elim_vale_sig_cons #code
                       (hd:vale_type)
                       (tl:list vale_type)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl code win pre post)
    : x:vale_type_as_type hd
    -> vale_sig_tl code win (elim_1 pre x) (elim_1 post x)
    = v

[@reduce]
let vale_sig (#dom:list vale_type)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:va_code ->
    win:bool ->
    vale_sig_tl code win (pre code win)
                     (post code win)

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////

unfold let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%reduce];
     delta_only [`%VT_Buffer?;
                 `%Mkstate?.ok;
                 `%Mkstate?.regs;
                 `%Mkstate?.xmms;
                 `%Mkstate?.flags;
                 `%Mkstate?.mem;
                 `%BS.Mkstate?.ok;
                 `%BS.Mkstate?.regs;
                 `%BS.Mkstate?.xmms;
                 `%BS.Mkstate?.flags;
                 `%BS.Mkstate?.mem;
                 `%TS.MktraceState?.state;
                 `%TS.MktraceState?.trace;
                 `%TS.MktraceState?.memTaint;
                 `%FStar.FunctionalExtensionality.on_dom;
                 `%FStar.FunctionalExtensionality.on;
                 `%Interop.list_disjoint_or_eq;
                 `%Interop.list_live
                 ];
     primops;
     simplify]
     x

[@reduce]
unfold
let prestate_hyp
    (h0:HS.mem)
    (acc:list b8{disjoint_or_eq_l acc /\ live_l h0 acc})
    (push_h0:HS.mem)
    (alloc_push_h0:HS.mem)
    (b:b8)
  : Type0 =
  HS.fresh_frame h0 push_h0 /\
  M.modifies M.loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  normal (mem_roots_p alloc_push_h0 (b::acc))

[@reduce]
let as_lowstar_sig_tl_req
    (acc:list b8)
    (down:create_vale_initial_state_t [] acc)
    (pre:vale_pre_tl [])
    (post:vale_post_tl [])
    (h0:HS.mem)
  : Type0 =
  mem_roots_p h0 acc /\
  (forall (push_h0:mem_roots acc) (alloc_push_h0:mem_roots acc) (b:stack_buffer).
    let b' = to_b8 b in
    prestate_hyp h0 acc push_h0 alloc_push_h0 b' ==>
    elim_nil pre (elim_down_nil acc down alloc_push_h0 b') b)

[@reduce]
let as_lowstar_sig_tl_ens
    (acc:list b8)
    (down:create_vale_initial_state_t [] acc)
    (pre:vale_pre_tl [])
    (post:vale_post_tl [])
    (h0:HS.mem)
    (_:unit)
    (h1:HS.mem)
  : Type0 =
  exists push_h0 alloc_push_h0 (b:stack_buffer) final (fuel:va_fuel).
    let b' = to_b8 b in
    mem_roots_p h0 acc /\
    prestate_hyp h0 acc push_h0 alloc_push_h0 b' /\ (
      let initial_state = elim_down_nil acc down alloc_push_h0 b' in
      elim_nil post initial_state b final fuel /\
      //not really needed: eval_code code initial_state fuel final /\
      HS.poppable (get_hs final.mem) /\
      h1 == HS.pop (get_hs final.mem))

[@reduce]
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
        (requires as_lowstar_sig_tl_req acc down pre post)
        (ensures as_lowstar_sig_tl_ens acc down pre post)
    | hd::tl ->
      x:vale_type_as_type hd ->
      as_lowstar_sig_tl
        #tl
        code
        (maybe_cons_buffer hd x acc)
        (elim_down_cons hd tl acc down x)
        (elim_1 pre x)
        (elim_1 post x)

[@reduce]
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

[@reduce]
let as_lowstar_sig  (c:va_code) (dom:list vale_type{List.length dom < max_arity win})
                    (pre: vale_pre dom)
                    (post: vale_post dom) =
    unit ->
    as_lowstar_sig_tl
      #dom
      c
      []
      (create_vale_initial_state win dom)
      (pre c win)
      (post c win)

////////////////////////////////////////////////////////////////////////////////

[@reduce]
let elim_vale_sig_nil  #code #win
                       (pre:vale_pre_tl [])
                       (post:vale_post_tl [])
                       (v:vale_sig_tl code win pre post)
    : va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) -> elim_nil post va_s0 stack_b va_s1 f))
    = v

[@reduce]
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

[@reduce]
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

val lower_code (c:va_code) : code

val wrap (code:va_code) (dom:list vale_type{List.length dom < max_arity win})
         (pre:vale_pre dom)
         (post:vale_post dom)
         (v:vale_sig pre post)
         (t_low:IS.as_lowstar_sig (lower_code code) dom)
  : as_lowstar_sig code dom pre post

//A couple of utilities for the library
let force (#a:Type) (x:a) : normal a = x
let elim_normal (p:Type) : Lemma (requires (normal p)) (ensures p) = ()

let elim_lowstar_sig (#code:va_code) (#dom:list vale_type{List.length dom < max_arity win})
                     (#pre:vale_pre dom)
                     (#post:vale_post dom)
                     (f:as_lowstar_sig code dom pre post)
    : normal (as_lowstar_sig code dom pre post)
    = force f

let hs_of_va_state (x:va_state) : HS.mem = get_hs x.mem

[@reduce]
let pre_in_prestate_ctx
       (h0:HS.mem)
       (acc:list b8{disjoint_or_eq_l acc /\ live_l h0 acc})
       (create_initial_state: (h:HS.mem -> b:b8{normal (mem_roots_p h (b::acc))} -> GTot va_state))
       (pre: (va_state -> b:stack_buffer -> Type)) =
      forall (push_h0:Monotonic.HyperStack.mem)
        (alloc_push_h0: Monotonic.HyperStack.mem)
        (b: stack_buffer).
          let b' = to_b8 b in
          prestate_hyp h0 acc push_h0 alloc_push_h0 b' ==>
          pre (create_initial_state alloc_push_h0 b') b

[@reduce]
let post_in_poststate_ctx
         (va_b0:va_code)
         (h0:HS.mem)
         (acc:list b8{disjoint_or_eq_l acc /\ live_l h0 acc})
         (create_initial_state: (h:HS.mem -> b:b8{normal (mem_roots_p h (b::acc))} -> GTot va_state))
         (post: va_state -> stack_buffer -> va_state -> va_fuel -> Type)
         (h1:HS.mem) =
      exists (push_h0:Monotonic.HyperStack.mem)
        (alloc_push_h0: Monotonic.HyperStack.mem)
        (b: stack_buffer)
        (final:va_state)
        (fuel:va_fuel).
          let b' = to_b8 b in
          prestate_hyp h0 acc push_h0 alloc_push_h0 b' ==>
          (let initial_state = create_initial_state alloc_push_h0 b' in
           post initial_state b final fuel /\
           //not really needed: eval_code va_b0 initial_state fuel final /\
           Monotonic.HyperStack.poppable (hs_of_va_state final) /\
           h1 == Monotonic.HyperStack.pop (hs_of_va_state final))
