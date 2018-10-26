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

[@unifier_hint_injective]
let rec n_arrow (dom:list vale_type) (codom:Type) =
  match dom with
  | [] -> codom
  | hd::tl -> vale_type_as_type hd -> n_arrow tl codom

let rec as_tuple (dom:list vale_type{Cons? dom}) =
  match dom with
  | [x] -> vale_type_as_type x
  | hd::tl -> vale_type_as_type hd & as_tuple tl

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

[@unifier_hint_injective]
let rec n_dep_arrow (dom:list vale_type) (codom: n_arrow dom Type) =
  match dom with
  | [] -> codom
  | hd::tl -> x:vale_type_as_type hd -> n_dep_arrow tl (elim_1 codom x)

let rec dom_as_tuple (acc:Type) (dom:list vale_type)
  : Tot Type (decreases dom) =
  match dom with
  | [] -> acc
  | hd::tl -> dom_as_tuple (acc & vale_type_as_type hd) tl

[@unifier_hint_injective]
let arr (dom:Type) (codom:Type) = dom -> codom

let rec n_dep_arrow_uncurry
        (prefix: Type)
        (v:prefix)
        (dom:list vale_type)
        (codom: arr (dom_as_tuple prefix dom) Type)
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

let vale_pre_tl (dom:list vale_type) =
    n_arrow dom prop

let vale_pre (dom:list vale_type) =
    code:va_code ->
    s0:va_state ->
    win:bool ->
    stack:buffer (TBase TUInt64) ->
    vale_pre_tl dom

let vale_post_tl (dom:list vale_type) =
    n_arrow dom (s1:va_state -> f:va_fuel -> prop)

let vale_post (dom:list vale_type) =
    code:va_code ->
    s0:va_state ->
    win:bool ->
    stack:buffer (TBase TUInt64) ->
    vale_post_tl dom

let rec vale_sig_tl (#dom:list vale_type{Cons? dom})
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [hd] ->
      x:vale_type_as_type hd ->
      Ghost (va_state & va_fuel)
            (requires (elim_1 pre x))
            (ensures (fun (s1, f) -> elim_nil (elim_1 post x) s1 f))
    | hd::tl ->
      x:vale_type_as_type hd ->
      vale_sig_tl #tl (elim_1 pre x) (elim_1 post x)

let vale_sig (#dom:list vale_type{Cons? dom})
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    va_b0:va_code ->
    va_s0:va_state ->
    win:bool ->
    stack_b:buffer64 ->
    vale_sig_tl (pre va_b0 va_s0 win stack_b)
                (post va_b0 va_s0 win stack_b)

let rec create_buffer_list (dom:list vale_type) (acc:list b8)
    : n_arrow dom (list b8) =
    match dom with
    | [] -> acc
    | hd::tl ->
      (fun (x:vale_type_as_type hd) -> create_buffer_list tl (if VT_Buffer? hd then x::acc else acc))


// let create_buffer_list (dst:b8) (src:b8) (stack_b:b8)  : (l:list b8{
//     l == [stack_b;dst;src] /\
//   (forall x. {:pattern List.memP x l} List.memP x l <==> (x == dst \/ x == src \/ x == stack_b))}) =
//   [stack_b;dst;src]
let maybe_cons_buffer (a:vale_type) (x:vale_type_as_type a) (acc:list b8) : list b8 =
  if VT_Buffer? a then x::acc else acc

let rec initial_state_t
              (dom:list vale_type)
              (acc:list b8)
              (codom:Type)
  : n_arrow dom Type =
    match dom with
    | [] ->
      (h0:HS.mem{ Interop.list_disjoint_or_eq acc /\
                  Interop.list_live h0 acc } ->
       GTot codom)
    | hd::tl ->
      fun (x:vale_type_as_type hd) ->
         initial_state_t tl (maybe_cons_buffer hd x acc) codom

let fold_initial_state_t
  (#hd:vale_type) (#tl:list vale_type)
  (#x:vale_type_as_type hd) (#acc:list b8) (#codom:Type)
  (res:n_dep_arrow tl (initial_state_t tl (maybe_cons_buffer hd x acc) codom))
  : n_dep_arrow tl (elim_1 (initial_state_t (hd::tl) acc codom) x)
  = res

let initial_trusted_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc (TS.traceState & mem)

let intro_n_arrow_nil (a:Type) (x:a)
  : n_arrow [] a
  = x

let intro_n_arrow_cons (hd:vale_type) (b:Type) (tl:list vale_type)
                       (x:vale_type_as_type hd -> n_arrow tl b)
  : n_arrow (hd::tl) b
  = x

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

let test : n_dep_arrow [VT_Base TUInt8] (fun (x:UInt8.t) -> y:UInt8.t{x == y}) =
  fun (x:UInt8.t) -> intro_dep_arrow_nil (y:UInt8.t{x == y}) x

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
      | VT_Base TUInt128 ->
        0 //IMPOSSIBLE
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

let create_initial_trusted_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem{ Interop.list_disjoint_or_eq acc /\
                   Interop.list_live h0 acc })
  : GTot (TS.traceState & mem)
  = let (mem:mem) = {
      addrs = addrs;
      ptrs = acc;
      hs = h0
    } in
    let regs = FunctionalExtensionality.on reg regs in
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

let mem_roots (roots:list b8) =
    h0:HS.mem{ Interop.list_disjoint_or_eq roots /\
               Interop.list_live h0 roots }

let rec create_initial_state_aux
        #codom
        (dom:list vale_type)
        (is_win:bool)
        (i:nat{i + List.length dom < max_arity is_win})
        (regs:registers)
        (xmms:xmms_t)
        (acc:list b8)
        (taint:taint_map)
        (f: (acc:list b8 -> registers -> xmms_t -> taint_map -> mem_roots acc -> GTot codom))
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

let init_regs (stack_b:b8) : registers =
    fun r ->
      if r = Rsp then
        addrs stack_b
      else init_regs r

let create_initial_trusted_state
      (is_win:bool)
      (stack_b:b8)
      (dom:list vale_type{List.length dom < max_arity is_win})
    : n_dep_arrow
         dom
         (initial_trusted_state_t dom [stack_b])
    = create_initial_state_aux
          dom
          is_win
          0
          (init_regs stack_b)
          init_xmms
          [stack_b]
          init_taint
          create_initial_trusted_state_core

let initial_vale_state_t (dom:list vale_type) (acc:list b8) =
  initial_state_t dom acc va_state

let create_initial_vale_state_core
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:HS.mem{ Interop.list_disjoint_or_eq acc /\
                   Interop.list_live h0 acc })
  : GTot va_state
  = let t_state, mem = create_initial_trusted_state_core acc regs xmms taint h0 in
    {ok = TS.(BS.(t_state.state.ok));
     regs = X64.Vale.Regs.of_fun TS.(BS.(t_state.state.regs));
     xmms =  X64.Vale.Xmms.of_fun TS.(BS.(t_state.state.xmms));
     flags = TS.(BS.(t_state.state.flags));
     mem = mem;
     memTaint = TS.(t_state.memTaint)}

let create_initial_vale_state
       (is_win:bool)
       (stack_b:b8)
       (dom:list vale_type{List.length dom < max_arity is_win})
    : n_dep_arrow
         dom
         (initial_vale_state_t dom [stack_b])
     = create_initial_state_aux
           dom
           is_win
           0
           (init_regs stack_b)
           init_xmms
           [stack_b]
           init_taint
           create_initial_vale_state_core

let core_create_lemma
       (acc:list b8)
       (regs:registers)
       (xmms:xmms_t)
       (taint:taint_map)
       (h0:mem_roots acc)
  : Lemma
      (ensures (fst (create_initial_trusted_state_core acc regs xmms taint h0) ==
                state_to_S (create_initial_vale_state_core acc regs xmms taint h0)))
  = let s_init, _ = (create_initial_trusted_state_core acc regs xmms taint h0) in
    let s0 = (create_initial_vale_state_core acc regs xmms taint h0) in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))
