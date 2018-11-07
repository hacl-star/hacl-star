module X64.Interop_s

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
//open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
//open X64.Vale.State
//open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
//open X64.Vale.StateLemmas
//open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory_s
module BS = X64.Bytes_Semantics_s

friend X64.Memory_s
friend X64.Memory
//friend X64.Vale.Decls
//friend X64.Vale.StateLemmas

unfold let code = TS.tainted_code

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

//The type of an arity-generic function that produces a pair
//of related trusted and vale states
let trusted_initial_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc (TS.traceState & mem)

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

let create_trusted_initial_state_t (dom:list vale_type)
                                (acc:list b8)
    = n_dep_arrow
          dom
          (initial_trusted_state_t dom acc)

let create_trusted_initial_state
      (is_win:bool)
      (dom:list vale_type{List.length dom < max_arity is_win})
    : create_trusted_initial_state_t dom []
    = create_initial_state_aux
          dom
          is_win
          0
          init_regs
          init_xmms
          []
          init_taint
          create_initial_trusted_state_core

let stack_buffer = buffer (TBase TUInt64)

//////////////////////////////////////////////////////////////////////////////////////////
//lowstar_sig pre post:
//    Interepreting a vale pre/post as a Low* function type
//////////////////////////////////////////////////////////////////////////////////////////

let elim_down_1 (hd:vale_type)
                (acc:list b8)
                (down:create_trusted_initial_state_t [hd] acc)
                (x:vale_type_as_type hd)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::maybe_cons_buffer hd x acc)} -> GTot (TS.traceState & mem) =
    down x

let elim_down_nil (acc:list b8)
                  (down:create_trusted_initial_state_t [] acc)
    : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::acc)} -> GTot (TS.traceState & mem) =
    down

let elim_down_cons (hd:vale_type)
                   (tl:list vale_type)
                   (acc:list b8)
                   (down:create_trusted_initial_state_t (hd::tl) acc)
                   (x:vale_type_as_type hd)
    : create_trusted_initial_state_t tl (maybe_cons_buffer hd x acc) =
    elim_dep_arrow_cons hd tl down x

// (stack_bytes:nat)
// stack_b:b8 ->
let wrap_pre (c:code) (acc:list b8) (down:create_trusted_initial_state_t [] acc) (h0:HS.mem) =
  s0:TS.traceState ->
  push_h0:mem_roots acc ->
  alloc_push_h0:mem_roots acc ->
  b:stack_buffer{mem_roots_p alloc_push_h0 (b::acc)} ->
  Ghost (nat & mem)
    (requires
      HS.fresh_frame h0 push_h0 /\
      M.modifies loc_none push_h0 alloc_push_h0 /\
      HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
      B.frameOf b == HS.get_tip alloc_push_h0 /\
      B.live alloc_push_h0 b /\
      s0 == fst (elim_down_nil acc down alloc_push_h0 b)
    )
    (ensures fun (fuel, final_mem) ->
      Some? (TS.taint_eval_code c fuel s0)
  // TODO: down_mem final_mem.hs == (TS.taint_eval_code c fuel s0).TS.state.mem
  // TODO: ok
  // TODO: callee-save
    )

let as_lowstar_sig_post
    (acc:list b8)
    (h0:HS.mem)
    (push_h0:mem_roots acc)
    (alloc_push_h0:mem_roots acc)
    (b:stack_buffer)
    (h1:HS.mem) =
  HS.fresh_frame h0 push_h0 /\
  M.modifies loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
//  HS.poppable final.mem.hs /\
//                            h1 == HS.pop (final.mem.hs) /\
  True

let rec as_lowstar_sig_tl
  (c:code)
  (dom:list vale_type)
                          (acc:list b8)
                          (down:create_trusted_initial_state_t dom acc)
    : Type =
    match dom with
    | [] ->
      (h0:HS.mem) ->
      wrap_pre c acc down h0 ->
      Stack (mem_roots acc & mem_roots acc & stack_buffer)
        (requires (fun h0' -> h0 == h0' /\
                    mem_roots_p h0 acc /\
//                    (forall (push_h0:mem_roots acc)
//                       (alloc_push_h0:mem_roots acc)
//                       (b:stack_buffer).
//                            HS.fresh_frame h0 push_h0 /\
//                            M.modifies loc_none push_h0 alloc_push_h0 /\
//                            HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
//                            B.frameOf b == HS.get_tip alloc_push_h0 /\
//                            B.live alloc_push_h0 b ==>
//                            elim_nil pre (elim_down_nil acc down alloc_push_h0 b) b)))
True))
        (ensures fun h0 (push_h0, alloc_push_h0, b) h1 ->
          as_lowstar_sig_post acc h0 push_h0 alloc_push_h0 b h1
        )
//                       exists (push_h0:mem_roots acc) (alloc_push_h0:mem_roots acc) (b:stack_buffer) final.// fuel.//  {:pattern
//                                 // (post push_h0 alloc_push_h0 b final fuel)}
//                            HS.fresh_frame h0 push_h0 /\
//                            M.modifies loc_none push_h0 alloc_push_h0 /\
//                            HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
//                            B.frameOf b == HS.get_tip alloc_push_h0 /\
//                            B.live alloc_push_h0 b /\

//                            elim_nil
//                              post
//                              (elim_down_nil acc down alloc_push_h0 b)
//                              b
//                              final
//                              fuel /\

//                            HS.poppable final.mem.hs /\
//                            h1 == HS.pop (final.mem.hs) /\
//True
//                          ))

    | hd::tl ->
      x:vale_type_as_type hd ->
      as_lowstar_sig_tl
        c
        tl
        (maybe_cons_buffer hd x acc)
        (elim_down_cons hd tl acc down x)

let as_lowstar_sig (c:code) (dom:list vale_type{List.length dom < max_arity win}) =
    as_lowstar_sig_tl
      c
      dom
      []
      (create_trusted_initial_state win dom)

////////////////////////////////////////////////////////////////////////////////

let rec wrap_tl
         (c:code)
         (dom:list vale_type)
         (acc:list b8)
         (down:create_trusted_initial_state_t dom acc)
    : as_lowstar_sig_tl c dom acc down
    = match dom with
      | [] ->
        let f : as_lowstar_sig_tl c [] acc down =
          let ff (h0:HS.mem) (pre:wrap_pre c acc down h0) : Stack (mem_roots acc & mem_roots acc & stack_buffer)
            (requires (fun h0' -> h0 == h0' /\ mem_roots_p h0 acc /\ True))
            (ensures (fun h0 (push_h0, alloc_push_h0, b) h1 -> as_lowstar_sig_post acc h0 push_h0 alloc_push_h0 b h1))
            =
            let h0' = get () in
            push_frame ();
            let h1 = get () in
            let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
            let h2 = get () in
            assert (HS.fresh_frame h0 h1);
            assert (mem_roots_p h2 acc);
            st_put (fun h0' -> h0' == h2) (fun h0' ->
              let va_s0, mem_s0 = elim_down_nil acc down h0' stack_b in
              let (fuel, final_mem) = pre va_s0 h1 h2 stack_b in
              assert (B.frameOf stack_b = HS.get_tip h0');
              assert (B.live h0' stack_b);
              let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
              (), final_mem.hs
            ); //conveniently, st_put assumes that the shape of the stack did not change
            pop_frame ();
            (h1, h2, stack_b)
          in ff
(*
          fun (h0:HS.mem) (pre:wrap_pre c acc down h0) ->
            let h0' = get () in
            push_frame ();
            let h1 = get () in
            let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
            let h2 = get () in
            assert (HS.fresh_frame h0 h1);
            assert (mem_roots_p h2 acc);
            st_put (fun h0' -> h0' == h2) (fun h0' ->
              let va_s0, mem_s0 = elim_down_nil acc down h0' stack_b in
              let (fuel, final_mem) = pre va_s0 h1 h2 stack_b in
              assert (B.frameOf stack_b = HS.get_tip h0');
              assert (B.live h0' stack_b);
              let Some va_s1 = TS.taint_eval_code c fuel va_s0 in
              (), final_mem.hs
            ); //conveniently, st_put assumes that the shape of the stack did not change
            pop_frame ();
            (h1, h2, stack_b)
*)
        in
        f <: as_lowstar_sig_tl c [] acc down

      | hd::tl ->
        let f (x:vale_type_as_type hd)
           : as_lowstar_sig_tl c tl (maybe_cons_buffer hd x acc)
                               (elim_down_cons hd tl acc down x)
           = wrap_tl c tl
                  (maybe_cons_buffer hd x acc)
                  (elim_down_cons hd tl acc down x)
        in
        f


let wrap (c:code) (dom:list vale_type{List.length dom < max_arity win})
  : as_lowstar_sig c dom =
     wrap_tl c dom [] (create_trusted_initial_state win dom)

(*
////////////////////////////////////////////////////////////////////////////////
//test
////////////////////////////////////////////////////////////////////////////////
open Vale_memcpy
friend X64.Vale.Decls

let c : code = va_code_memcpy true

unfold
let dom : l:list vale_type{List.Tot.length l < max_arity win} =
  let d = [VT_Buffer TUInt64; VT_Buffer TUInt64;] in
  assert_norm (List.Tot.length d < max_arity win);
  d

let memcpy_raw
    : as_lowstar_sig c dom
    = wrap c dom

unfold let normal_steps : list string =
  [
    `%as_lowstar_sig;
    `%as_lowstar_sig_tl;
    `%vale_type_as_type;
    `%VT_Buffer?;
    `%maybe_cons_buffer;
    `%elim_down_cons;
    `%create_trusted_initial_state;
//    `%create_initial_state_aux;
//    `%elim_dep_arrow_nil;
//    `%elim_dep_arrow_cons;
  ]

unfold let normal (#a:Type) (x:a) : a = norm [iota; zeta; simplify; primops; delta_only normal_steps] x
//unfold let normal (#a:Type) (x:a) : a = norm [delta_only normal_steps] x

let force (#a:Type) (x:a) : normal a = x

#reset-options "--debug X64.Interop_s --debug_level print_normalized_terms --use_two_phase_tc false"
//let elim_lowstar_sig (dom:list vale_type{List.length dom < max_arity win})
//                     (f:as_lowstar_sig c dom)
//    : (assume False; normal (as_lowstar_sig c dom))
//    =
//admit ()
//    assume False;
//    force #(as_lowstar_sig c dom) f

val memcpy: dst:buffer64 -> src:buffer64 -> Stack unit
        (requires (fun h -> True))
        (ensures (fun h0 _ h1 -> True))
let memcpy dst src =
//  let f:normal (as_lowstar_sig c dom) = elim_lowstar_sig dom memcpy_raw in
//  let f:normal (as_lowstar_sig c dom) = force #(as_lowstar_sig c dom) memcpy_raw in
  let f1:normal (as_lowstar_sig c dom) = memcpy_raw in
  let f2 = f1 dst src in
  let h0 = get () in
  let f3 = f2 h0 in
//  f dst src ()
()
*)
