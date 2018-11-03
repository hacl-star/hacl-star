module GenericInterop

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

friend X64.Memory_s
friend X64.Memory
friend X64.Vale.Decls
friend X64.Vale.StateLemmas

////////////////////////////////////////////////////////////////////////////////
// Vale-specific types supported by the interop layer
//   Some integer types
//   And arrays thereof
////////////////////////////////////////////////////////////////////////////////

type vale_type =
  | VT_Base of X64.Memory_s.base_typ
  | VT_Buffer of X64.Memory_s.base_typ

#set-options "--initial_ifuel 1"
let base_type_as_type : X64.Memory_s.base_typ -> Type =
  function
  | TUInt8 -> UInt8.t
  | TUInt16 -> UInt16.t
  | TUInt32 -> UInt32.t
  | TUInt64 -> UInt64.t
  | TUInt128 -> False

let vale_type_as_type : vale_type -> Type =
  function
  | VT_Base bt -> base_type_as_type bt
  | VT_Buffer bt -> X64.Memory_s.buffer (TBase bt)


////////////////////////////////////////////////////////////////////////////////
// as_l/r_tuple: Interpreting a list of vale types as
//               a left- or right-nested pair
////////////////////////////////////////////////////////////////////////////////
let rec as_right_tuple (dom:list vale_type{Cons? dom}) =
  match dom with
  | [x] -> vale_type_as_type x
  | hd::tl -> vale_type_as_type hd & as_right_tuple tl

let rec as_left_tuple (acc:Type) (dom:list vale_type)
  : Tot Type (decreases dom) =
  match dom with
  | [] -> acc
  | hd::tl -> as_left_tuple (acc & vale_type_as_type hd) tl

////////////////////////////////////////////////////////////////////////////////
// n_arrow: Arrows with a generic number of vale types as the domain
//          and a result type `codom` that does not depend on the domain
////////////////////////////////////////////////////////////////////////////////
[@unifier_hint_injective]
let rec n_arrow (dom:list vale_type) (codom:Type) =
  match dom with
  | [] -> codom
  | hd::tl -> vale_type_as_type hd -> n_arrow tl codom

[@unifier_hint_injective]
let arr (dom:Type) (codom:Type) = dom -> codom

let elim_1 (#dom:list vale_type{Cons? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : vale_type_as_type (Cons?.hd dom) -> n_arrow (Cons?.tl dom) r =
    f

let elim_nil (#dom:list vale_type{Nil? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : r =
    f

let intro_n_arrow_nil (a:Type) (x:a)
  : n_arrow [] a
  = x

let intro_n_arrow_cons (hd:vale_type) (b:Type) (tl:list vale_type)
                       (x:vale_type_as_type hd -> n_arrow tl b)
  : n_arrow (hd::tl) b
  = x

////////////////////////////////////////////////////////////////////////////////
// n_dep_arrow: Arrows with a generic number of vale types as the domain
//              and a result type codom that depends on the domain
////////////////////////////////////////////////////////////////////////////////
[@unifier_hint_injective]
let rec n_dep_arrow (dom:list vale_type) (codom: n_arrow dom Type) =
  match dom with
  | [] -> codom
  | hd::tl -> x:vale_type_as_type hd -> n_dep_arrow tl (elim_1 codom x)

//unused
let rec n_dep_arrow_uncurry
        (prefix: Type)
        (v:prefix)
        (dom:list vale_type)
        (codom: arr (as_left_tuple prefix dom) Type)
  : Tot Type (decreases dom) =
  match dom with
  | [] -> codom v
  | hd::tl ->
    x:vale_type_as_type hd ->
    n_dep_arrow_uncurry
      (prefix & vale_type_as_type hd)
      (v, x)
      tl
      codom

let intro_dep_arrow_nil (b:Type)
                        (f:b)
  : n_dep_arrow [] b
  = f

let intro_dep_arrow_1 (a:vale_type)
                      (b:n_arrow [a] Type)
                      (f:(x:vale_type_as_type a -> elim_1 b x))
  : n_dep_arrow [a] b
  = f

let intro_dep_arrow_cons (hd:vale_type)
                         (tl:list vale_type)
                         (b: n_arrow (hd::tl) Type)
                         (f: (x:vale_type_as_type hd -> n_dep_arrow tl (elim_1 b x)))
  : n_dep_arrow (hd::tl) b
  = f

let elim_dep_arrow_nil (#codom:n_arrow [] Type)
                       (f:n_dep_arrow [] codom)
    : elim_nil codom
   = f

let elim_dep_arrow_cons (hd:vale_type)
                        (tl:list vale_type)
                        (#codom:n_arrow (hd::tl) Type)
                        (f:n_dep_arrow (hd::tl) codom)
    : x:vale_type_as_type hd ->
      n_dep_arrow tl (elim_1 codom x)
   = f

//Just a small test function to see how these coercions work
let test : n_dep_arrow [VT_Base TUInt8] (fun (x:UInt8.t) -> y:UInt8.t{x == y}) =
  fun (x:UInt8.t) -> intro_dep_arrow_nil (y:UInt8.t{x == y}) x

////////////////////////////////////////////////////////////////////////////////
// Creating initial states
// The punchline of this section is the `create_both_initial_states`,
// an arity generic function that builds a trusted state `t:TS.state`
// and a vale state `v:va_state` with a proof that `t == state_to_S v`
////////////////////////////////////////////////////////////////////////////////
let rec create_buffer_list (dom:list vale_type) (acc:list b8)
    : n_arrow dom (list b8) =
    match dom with
    | [] -> acc
    | hd::tl ->
      (fun (x:vale_type_as_type hd) -> create_buffer_list tl (if VT_Buffer? hd then x::acc else acc))

let maybe_cons_buffer (a:vale_type) (x:vale_type_as_type a) (acc:list b8) : list b8 =
  if VT_Buffer? a then x::acc else acc

let mem_roots_p (h0:HS.mem) (roots:list b8) =
  Interop.list_disjoint_or_eq roots /\
  Interop.list_live h0 roots

let mem_roots (roots:list b8) =
    h0:HS.mem{ mem_roots_p h0 roots }

let rec initial_state_t
              (dom:list vale_type)
              (acc:list b8)
              (codom:Type)
  : n_arrow dom Type =
    match dom with
    | [] ->
      (h0:HS.mem ->
       stack:b8{mem_roots_p h0 (stack::acc)} ->
       GTot codom)
    | hd::tl ->
      fun (x:vale_type_as_type hd) ->
         initial_state_t tl (maybe_cons_buffer hd x acc) codom

// Some identity coercions that serve as proof hints
// to introduce generic arrow types
let fold_initial_state_t
  (#hd:vale_type) (#tl:list vale_type)
  (#x:vale_type_as_type hd) (#acc:list b8) (#codom:Type)
  (res:n_dep_arrow tl (initial_state_t tl (maybe_cons_buffer hd x acc) codom))
  : n_dep_arrow tl (elim_1 (initial_state_t (hd::tl) acc codom) x)
  = res

let initial_trusted_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc (TS.traceState & mem)

////////////////////////////////////////////////////////////////////////////////
//The calling convention w.r.t the register mapping
////////////////////////////////////////////////////////////////////////////////
let max_arity (is_win:bool) = if is_win then 4 else 6

let register_of_arg_i (is_win:bool) (i:nat{i < max_arity is_win}) : reg =
  if is_win then
    match i with
    | 0 -> Rcx
    | 1 -> Rdx
    | 2 -> R8
    | 3 -> R9
  else
    match i with
    | 0 -> Rdi
    | 1 -> Rsi
    | 2 -> Rdx
    | 3 -> Rcx
    | 4 -> R8
    | 5 -> R9

//A partial inverse of the above function
let arg_of_register (is_win:bool) (r:reg)
  : option (i:nat{i < max_arity is_win /\ register_of_arg_i is_win i = r})
  = if is_win then
       match r with
       | Rcx -> Some 0
       | Rdx -> Some 1
       | R8 -> Some 2
       | R9 -> Some 3
       | _ -> None
    else
       match r with
       | Rdi -> Some 0
       | Rsi -> Some 1
       | Rdx -> Some 2
       | Rcx -> Some 3
       | R8 -> Some 4
       | R9 -> Some 5
       | _ -> None

let registers = reg -> nat64

let update_regs (#a:vale_type)
                (x:vale_type_as_type a)
                (is_win:bool)
                (i:nat{i < max_arity is_win})
                (regs:registers)
  : registers
  =
    let value : nat64 =
      match a with
      | VT_Base TUInt8 ->
        UInt8.v x
      | VT_Base TUInt16 ->
        UInt16.v x
      | VT_Base TUInt32 ->
        UInt32.v x
      | VT_Base TUInt64 ->
        UInt64.v x
      | VT_Buffer _ ->
        addrs x
    in
    fun (r:reg) ->
      match arg_of_register is_win r with
      | Some j ->
        if i = j then value
        else regs r
      | _ -> regs r

let xmms_t = xmm -> quad32

let taint_map = b8 -> GTot taint

let update_taint_map (#a:vale_type)
                     (x:vale_type_as_type a)
                     (taint:taint_map) =
    match a with
    | VT_Buffer _ ->
      fun (y:b8) ->
        if StrongExcludedMiddle.strong_excluded_middle ((x <: b8) == y) then
          Secret
        else taint y
    | _ -> taint

let regs_with_stack (regs:registers) (stack_b:b8) : registers =
    fun r ->
      if r = Rsp then
        addrs stack_b
      else regs r

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
  : GTot (TS.traceState & mem)
  = let acc = stack::acc in
    let (mem:mem) = {
      addrs = addrs;
      ptrs = acc;
      hs = h0
    } in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm xmms in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = 0;
      BS.mem = Interop.down_mem h0 addrs acc
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = create_valid_memtaint mem acc taint
    },
    mem

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

let create_both_initial_states_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem)
       (stack:b8{mem_roots_p h0 (stack::acc)})
    : GTot (t:TS.traceState &
            v:va_state{
              t == state_to_S v
            })
    = let t, _ = create_initial_trusted_state_core acc regs xmms taint h0 stack in
      let v = create_initial_vale_state_core acc regs xmms taint h0 stack in
      core_create_lemma acc regs xmms taint h0 stack;
      (|t, v|)

//The type of an arity-generic function that produces a pair
//of related trusted and vale states
let both_initial_states_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc (t:TS.traceState & v:va_state{t == state_to_S v})

//This function folds over the `dom:list vale_type`
//and builds an arity-generic dependent function that constructs
//the initial states
//It's maybe more generic than it needs to be, since it is now applied only
//once, i.e., with f = create_both_initial_states
let rec create_initial_state_aux
        #codom
        (dom:list vale_type)
        (is_win:bool)
        (i:nat{i + List.length dom < max_arity is_win})
        (regs:registers)
        (xmms:xmms_t)
        (acc:list b8)
        (taint:taint_map)
        (f: (acc:list b8 -> registers -> xmms_t -> taint_map -> h:HS.mem -> stack:b8{mem_roots_p h (stack::acc)} -> GTot codom))
      : n_dep_arrow
        dom
        (initial_state_t dom acc codom) =
        match dom with
        | [] ->
          //no more args; build the state from a HS.mem
          intro_dep_arrow_nil
              (initial_state_t [] acc codom)
              (f acc regs xmms taint)

        | hd::tl ->
          //put the next arg hd in the ith register
          //update the taint map
          //maybe add the next arg to the list of buffers
          //recur
          intro_dep_arrow_cons
              hd
              tl
              (initial_state_t dom acc codom)
              (fun (x:vale_type_as_type hd) ->
                fold_initial_state_t
                  (create_initial_state_aux
                    tl
                    is_win
                    (i + 1)
                    (update_regs x is_win i regs)
                    xmms
                    (maybe_cons_buffer hd x acc)
                    (update_taint_map x taint)
                    f))

let init_taint : taint_map = fun r -> Public

let create_both_initial_states
      (is_win:bool)
      (dom:list vale_type{List.length dom < max_arity is_win})
    : n_dep_arrow
         dom
         (both_initial_states_t dom [])
    = create_initial_state_aux
          dom
          is_win
          0
          init_regs
          init_xmms
          []
          init_taint
          create_both_initial_states_core

let create_vale_initial_state_t (dom:list vale_type)
                                (acc:list b8)
    = n_dep_arrow
          dom
          (initial_vale_state_t dom acc)

let create_vale_initial_state (dom:list vale_type{List.length dom < max_arity win})
                              (acc:list b8)
  : create_vale_initial_state_t dom
                                acc
  = create_initial_state_aux
          dom
          win
          0
          Interop_assumptions.init_regs
          init_xmms
          acc
          init_taint
          create_initial_vale_state_core

//////////////////////////////////////////////////////////////////////////////////////////
//vale_sig pre post: a template for a top-level signature provided by a vale function
//////////////////////////////////////////////////////////////////////////////////////////
let stack_buffer = buffer (TBase TUInt64)

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

let rec vale_sig_tl (#dom:list vale_type)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) -> elim_nil post va_s0 stack_b va_s1 f))

    | hd::tl ->
      x:vale_type_as_type hd ->
      vale_sig_tl #tl (elim_1 pre x) (elim_1 post x)

let elim_vale_sig_cons (hd:vale_type)
                       (tl:list vale_type)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl pre post)
    : x:vale_type_as_type hd
    -> vale_sig_tl (elim_1 pre x) (elim_1 post x)
    = v

let vale_sig (#dom:list vale_type)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    va_b0:va_code ->
    win:bool ->
    vale_sig_tl (pre va_b0 win)
                (post va_b0 win)

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////

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

let rec as_lowstar_sig_tl (#dom:list vale_type)
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
                            elim_nil
                              post
                              (elim_down_nil acc down alloc_push_h0 b)
                              b
                              final
                              fuel /\
                            HS.poppable final.mem.hs /\
                            h1 == HS.pop (final.mem.hs)))

    | hd::tl ->
      x:vale_type_as_type hd ->
      as_lowstar_sig_tl
        #tl
        (maybe_cons_buffer hd x acc)
        (elim_down_cons hd tl acc down x)
        (elim_1 pre x)
        (elim_1 post x)

let as_lowstar_sig  (#dom:list vale_type{List.length dom < max_arity win})
                    (pre: vale_pre dom)
                    (post: vale_post dom) =
    va_b0:va_code ->
    as_lowstar_sig_tl
      #dom
      []
      (create_vale_initial_state dom [])
      (pre va_b0 win)
      (post va_b0 win)

////////////////////////////////////////////////////////////////////////////////


let elim_vale_sig_nil  (pre:vale_pre_tl [])
                       (post:vale_post_tl [])
                       (v:vale_sig_tl pre post)
    : va_s0:va_state ->
      stack_b:stack_buffer ->
      Ghost (va_state & va_fuel)
            (requires (elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) -> elim_nil post va_s0 stack_b va_s1 f))
    = v

let rec wrap_tl
         (dom:list vale_type)
         (acc:list b8)
         (down:create_vale_initial_state_t dom acc)
         (pre:vale_pre_tl dom)
         (post:vale_post_tl dom)
         (v:vale_sig_tl pre post)
    : as_lowstar_sig_tl acc down pre post
    = match dom with
      | [] ->
        let f : as_lowstar_sig_tl #[] acc down pre post =
          fun () ->
            let h0 = get() in
            push_frame();
            let h1 = get () in
            let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
            let h2 = get () in
            assert (HS.fresh_frame h0 h1);
            assert (mem_roots_p h2 acc);
            st_put (fun h0' -> h0' == h2) (fun h0' ->
              let va_s0 = elim_down_nil acc down h0' stack_b in
              assert (B.frameOf stack_b = HS.get_tip h0');
              assert (B.live h0' stack_b);
              assert (elim_nil pre (elim_down_nil acc down h0' stack_b) stack_b);
              let va_s1, fuel = elim_vale_sig_nil pre post v va_s0 stack_b in
              assert (elim_nil post va_s0 stack_b va_s1 fuel);
              (), va_s1.mem.hs
            ); //conveniently, st_put assumes that the shape of the stack did not change
            pop_frame()
        in
        f <: as_lowstar_sig_tl #[] acc down pre post

      | hd::tl ->
        let f (x:vale_type_as_type hd)
           : as_lowstar_sig_tl (maybe_cons_buffer hd x acc)
                               (elim_down_cons hd tl acc down x)
                               (elim_1 pre x)
                               (elim_1 post x)
           = wrap_tl tl
                  (maybe_cons_buffer hd x acc)
                  (elim_down_cons hd tl acc down x)
                  (elim_1 pre x)
                  (elim_1 post x)
                  (elim_vale_sig_cons hd tl pre post v x)
        in
        f


let wrap (dom:list vale_type{List.length dom < max_arity win})
         (pre:vale_pre dom)
         (post:vale_post dom)
         (v:vale_sig pre post)
  : as_lowstar_sig pre post =
  fun (va_b0:va_code) ->
     wrap_tl dom [] (create_vale_initial_state dom []) (pre va_b0 win) (post va_b0 win) (v va_b0 win)

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
