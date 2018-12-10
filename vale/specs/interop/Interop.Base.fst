module Interop.Base

module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module LU = LowStar.Util
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
let reduce = ()

//type descriptors
type td =
  | TD_Base of ME.base_typ
  | TD_Buffer of ME.base_typ

unfold 
let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%reduce];
     delta_only [`%TD_Buffer?;
                 `%BS.Mkstate?.ok;
                 `%BS.Mkstate?.regs;
                 `%BS.Mkstate?.xmms;
                 `%BS.Mkstate?.flags;
                 `%BS.Mkstate?.mem;
                 `%TS.MktraceState?.state;
                 `%TS.MktraceState?.trace;
                 `%TS.MktraceState?.memTaint;
                 `%FStar.FunctionalExtensionality.on_dom;
                 `%FStar.FunctionalExtensionality.on// ;
                 // `%Interop.list_disjoint_or_eq;
                 // `%Interop.list_live
                 ];
     primops;
     simplify]
     x

////////////////////////////////////////////////////////////////////////////////

#set-options "--initial_ifuel 1"
[@reduce]
let base_typ_as_type : X64.Memory.base_typ -> Type =
  let open ME in
  function
  | TUInt8 -> UInt8.t
  | TUInt16 -> UInt16.t
  | TUInt32 -> UInt32.t
  | TUInt64 -> UInt64.t
  | TUInt128 -> False

[@reduce]
let td_as_vale_type : td -> Type =
  let open ME in
  function
  | TD_Base bt -> base_typ_as_type bt
  | TD_Buffer bt -> ME.buffer (TBase bt)

////////////////////////////////////////////////////////////////////////////////
// n_arrow: Arrows with a generic number of vale types as the domain
//          and a result type `codom` that does not depend on the domain
////////////////////////////////////////////////////////////////////////////////
[@(unifier_hint_injective) (reduce)]
let rec n_arrow (dom:list td) (codom:Type) =
  match dom with
  | [] -> codom
  | hd::tl -> td_as_vale_type hd -> n_arrow tl codom

[@(unifier_hint_injective) (reduce)]
let arr (dom:Type) (codom:Type) = dom -> codom

[@reduce]
let elim_1 (#dom:list td{Cons? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : td_as_vale_type (Cons?.hd dom) -> n_arrow (Cons?.tl dom) r =
    f

[@reduce]
let elim_nil (#dom:list td{Nil? dom})
           (#r:Type)
           (f:n_arrow dom r)
    : r =
    f

[@reduce]
let intro_n_arrow_nil (a:Type) (x:a)
  : n_arrow [] a
  = x

[@reduce]
let intro_n_arrow_cons (hd:td) (b:Type) (tl:list td)
                       (x:td_as_vale_type hd -> n_arrow tl b)
  : n_arrow (hd::tl) b
  = x

////////////////////////////////////////////////////////////////////////////////
// n_dep_arrow: Arrows with a generic number of vale types as the domain
//              and a result type codom that depends on the domain
////////////////////////////////////////////////////////////////////////////////
[@(unifier_hint_injective) (reduce)]
let rec n_dep_arrow (dom:list td) (codom: n_arrow dom Type) =
  match dom with
  | [] -> codom
  | hd::tl -> x:td_as_vale_type hd -> n_dep_arrow tl (elim_1 codom x)

[@reduce]
let intro_dep_arrow_nil (b:Type)
                        (f:b)
  : n_dep_arrow [] b
  = f

[@reduce]
let intro_dep_arrow_1 (a:td)
                      (b:n_arrow [a] Type)
                      (f:(x:td_as_vale_type a -> elim_1 b x))
  : n_dep_arrow [a] b
  = f

[@reduce]
let intro_dep_arrow_cons (hd:td)
                         (tl:list td)
                         (b: n_arrow (hd::tl) Type)
                         (f: (x:td_as_vale_type hd -> n_dep_arrow tl (elim_1 b x)))
  : n_dep_arrow (hd::tl) b
  = f

[@reduce]
let elim_dep_arrow_nil (#codom:n_arrow [] Type)
                       (f:n_dep_arrow [] codom)
    : elim_nil codom
   = f

[@reduce]
let elim_dep_arrow_cons (hd:td)
                        (tl:list td)
                        (#codom:n_arrow (hd::tl) Type)
                        (f:n_dep_arrow (hd::tl) codom)
    : x:td_as_vale_type hd ->
      n_dep_arrow tl (elim_1 codom x)
   = f

//Just a small test function to see how these coercions work
let __test : n_dep_arrow [TD_Base ME.TUInt8] (fun (x:UInt8.t) -> y:UInt8.t{x == y}) =
  fun (x:UInt8.t) -> intro_dep_arrow_nil (y:UInt8.t{x == y}) x

////////////////////////////////////////////////////////////////////////////////
let view_n (x:ME.typ) =
  let open ME in
  match x with
  | TBase TUInt8 -> 1
  | TBase TUInt16 -> 2
  | TBase TUInt32 -> 4
  | TBase TUInt64 -> 8
  | TBase TUInt128 -> 16

let lowstar_buffer (t:ME.typ) = b:B.buffer UInt8.t{B.length b % view_n t == 0}

//TODO: This should be provided by X64.Memory
let buffer_equiv (t:ME.typ)
  : Lemma (ME.buffer t == lowstar_buffer t)
  = admit()

[@reduce]
let coerce (x:'a{'a == 'b}) : 'b = x

[@reduce]
let as_lowstar_buffer (#t:ME.typ) (x:ME.buffer t)
  : Tot (lowstar_buffer t)
  = buffer_equiv t;
    coerce x

[@reduce]
let as_vale_buffer (#t:ME.typ) (x:lowstar_buffer t)
  : Tot (b:ME.buffer t)
  = buffer_equiv t;
    coerce x

////////////////////////////////////////////////////////////////////////////////
let b8 = B.buffer UInt8.t

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 ||
  addr2 + length2 < addr1

type addr_map = m:(b8 -> ME.nat64){
  (forall (buf1 buf2:b8).{:pattern (m buf1); (m buf2)} 
    B.disjoint buf1 buf2 ==> 
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
  (forall (b:b8).{:pattern (m b)} m b + B.length b < MS.pow2_64)}

// open LowStar.Buffer
// module B = LowStar.Buffer
// module BV = LowStar.BufferView
// open LowStar.Modifies
// module M = LowStar.Modifies
// open LowStar.ModifiesPat
// open FStar.HyperStack.ST
// module HS = FStar.HyperStack
// //open Interop
// open Words_s
// open Types_s
// open X64.Machine_s
// open X64.Memory
// open BufferViewHelpers
// open Interop_assumptions

// // === for refinement types
// noeq type h_equals_refine (a:Type) (x:a) : b:Type -> y:b -> Type =
//   | HReflRefine : p:(a -> Type0) -> q:squash (p x) -> h_equals_refine a x (y:a{p y}) x

// unfold let code = TS.tainted_code
// unfold let b8 = Interop.b8
// val to_b8 (#bt:ME.base_typ) (m:ME.buffer (TBase bt)) : m':b8{h_equals_refine b8 m' (ME.buffer (TBase bt)) m}

// ////////////////////////////////////////////////////////////////////////////////
// // Vale-specific types supported by the interop layer
// //   Some integer types
// //   And arrays thereof
// ////////////////////////////////////////////////////////////////////////////////

// let reduce = ()


// #set-options "--initial_ifuel 1"
// [@reduce]
// let base_typ_as_type : X64.Memory.base_typ -> Type =
//   function
//   | TUInt8 -> UInt8.t
//   | TUInt16 -> UInt16.t
//   | TUInt32 -> UInt32.t
//   | TUInt64 -> UInt64.t
//   | TUInt128 -> False


// ////////////////////////////////////////////////////////////////////////////////
// // as_l/r_tuple: Interpreting a list of vale types as
// //               a left- or right-nested pair
// ////////////////////////////////////////////////////////////////////////////////
// let rec as_right_tuple (dom:list td{Cons? dom}) =
//   match dom with
//   | [x] -> td_as_vale_type x
//   | hd::tl -> td_as_vale_type hd & as_right_tuple tl

// let rec as_left_tuple (acc:Type) (dom:list td)
//   : Tot Type (decreases dom) =
//   match dom with
//   | [] -> acc
//   | hd::tl -> as_left_tuple (acc & td_as_vale_type hd) tl


// ////////////////////////////////////////////////////////////////////////////////
// // Creating initial states
// // The punchline of this section is the `create_both_initial_states`,
// // an arity generic function that builds a trusted state `t:TS.state`
// // and a vale state `v:va_state` with a proof that `t == state_to_S v`
// ////////////////////////////////////////////////////////////////////////////////

// [@reduce]
// let maybe_cons_buffer (a:td) (x:td_as_vale_type a) (acc:list b8) : list b8 =
//   match a with TD_Buffer bt -> (to_b8 #bt x)::acc | _ -> acc

// [@reduce]
// let rec disjoint_or_eq_l_aux (b:b8) (rest:list b8) =
//     match rest with
//     | [] -> True
//     | hd::tl -> Interop.disjoint_or_eq b hd /\ disjoint_or_eq_l_aux b tl

// [@reduce]
// let rec disjoint_or_eq_l (roots:list b8) =
//   match roots with
//   | [] -> True
//   | hd::tl -> disjoint_or_eq_l_aux hd tl /\ disjoint_or_eq_l tl

// [@reduce]
// let rec live_l (h:HS.mem) (bs:list b8) =
//   match bs with
//   | [] -> True
//   | hd::tl -> live h hd /\ live_l h tl

// val equiv_disjoint_or_eq_l (roots:list b8)
//   : Lemma (ensures (disjoint_or_eq_l roots <==> Interop.list_disjoint_or_eq roots))
//           [SMTPatOr [[SMTPat (disjoint_or_eq_l roots)];
//                      [SMTPat (Interop.list_disjoint_or_eq roots)]]]

// val equiv_live_l (h:HS.mem) (roots:list b8)
//   : Lemma (ensures (live_l h roots <==> Interop.list_live h roots))
//           [SMTPatOr [[SMTPat (live_l h roots)];
//                      [SMTPat (Interop.list_live h roots)]]]

// [@reduce]
// let mem_roots_p (h0:HS.mem) (roots:list b8) =
//   disjoint_or_eq_l roots /\
//   live_l h0 roots

// [@reduce]
// let mem_roots (roots:list b8) =
//     h0:HS.mem{ mem_roots_p h0 roots }

// [@reduce]
// let rec initial_state_t
//               (dom:list td)
//               (acc:list b8)
//               (codom:Type)
//   : n_arrow dom Type =
//     match dom with
//     | [] ->
//       (h0:HS.mem ->
//        stack:b8{mem_roots_p h0 (stack::acc)} ->
//        GTot codom)
//     | hd::tl ->
//       fun (x:td_as_vale_type hd) ->
//          initial_state_t tl (maybe_cons_buffer hd x acc) codom

// // Some identity coercions that serve as proof hints
// // to introduce generic arrow types
// [@reduce]
// let fold_initial_state_t
//   (#hd:td) (#tl:list td)
//   (#x:td_as_vale_type hd) (#acc:list b8) (#codom:Type)
//   (res:n_dep_arrow tl (initial_state_t tl (maybe_cons_buffer hd x acc) codom))
//   : n_dep_arrow tl (elim_1 (initial_state_t (hd::tl) acc codom) x)
//   = res

// [@reduce]
// let initial_trusted_state_t (dom:list td) (acc:list b8) =
//   initial_state_t dom acc (TS.traceState & mem)

// ////////////////////////////////////////////////////////////////////////////////
// //The calling convention w.r.t the register mapping
// ////////////////////////////////////////////////////////////////////////////////
// let max_arity (is_win:bool) = if is_win then 4 else 6

// [@reduce]
// let register_of_arg_i (is_win:bool) (i:nat{i < max_arity is_win}) : reg =
//   if is_win then
//     match i with
//     | 0 -> Rcx
//     | 1 -> Rdx
//     | 2 -> R8
//     | 3 -> R9
//   else
//     match i with
//     | 0 -> Rdi
//     | 1 -> Rsi
//     | 2 -> Rdx
//     | 3 -> Rcx
//     | 4 -> R8
//     | 5 -> R9

// //A partial inverse of the above function
// [@reduce]
// let arg_of_register (is_win:bool) (r:reg)
//   : option (i:nat{i < max_arity is_win /\ register_of_arg_i is_win i = r})
//   = if is_win then
//        match r with
//        | Rcx -> Some 0
//        | Rdx -> Some 1
//        | R8 -> Some 2
//        | R9 -> Some 3
//        | _ -> None
//     else
//        match r with
//        | Rdi -> Some 0
//        | Rsi -> Some 1
//        | Rdx -> Some 2
//        | Rcx -> Some 3
//        | R8 -> Some 4
//        | R9 -> Some 5
//        | _ -> None

// let registers = reg -> nat64

// let upd_reg (is_win:bool) (regs:registers) (i:nat) (v:_) : registers =
//     fun (r:reg) ->
//       match arg_of_register is_win r with
//       | Some j ->
//         if i = j then v
//         else regs r
//       | _ -> regs r

// [@reduce]
// let update_regs (#a:td)
//                 (x:td_as_vale_type a)
//                 (is_win:bool)
//                 (i:nat{i < max_arity is_win})
//                 (regs:registers)
//   : registers
//   =
//     let value : nat64 =
//       match a with
//       | TD_Base TUInt8 ->
//         UInt8.v x
//       | TD_Base TUInt16 ->
//         UInt16.v x
//       | TD_Base TUInt32 ->
//         UInt32.v x
//       | TD_Base TUInt64 ->
//         UInt64.v x
//       | TD_Buffer bt ->
//         addrs (to_b8 #bt x)
//     in
//     upd_reg is_win regs i value

// let xmms_t = xmm -> quad32

// let taint_map = b8 -> GTot taint

// let upd_taint_map (taint:taint_map) (x:b8) : taint_map =
//       fun (y:b8) ->
//         if StrongExcludedMiddle.strong_excluded_middle ((x <: b8) == y) then
//           Secret
//         else taint y

// [@reduce]
// let update_taint_map (#a:td)
//                      (x:td_as_vale_type a)
//                      (taint:taint_map) =
//     match a with
//     | TD_Buffer bt ->
//       upd_taint_map taint (to_b8 #bt x)
//     | _ -> taint

// let regs_with_stack (regs:registers) (stack_b:b8) : registers =
//     fun r ->
//       if r = Rsp then
//         addrs stack_b
//       else regs r

// unfold let normal (#a:Type) (x:a) : a =
//   FStar.Pervasives.norm
//     [iota;
//      zeta;
//      delta_attr [`%reduce];
//      delta_only [`%TD_Buffer?;
//                  `%BS.Mkstate?.ok;
//                  `%BS.Mkstate?.regs;
//                  `%BS.Mkstate?.xmms;
//                  `%BS.Mkstate?.flags;
//                  `%BS.Mkstate?.mem;
//                  `%TS.MktraceState?.state;
//                  `%TS.MktraceState?.trace;
//                  `%TS.MktraceState?.memTaint;
//                  `%FStar.FunctionalExtensionality.on_dom;
//                  `%FStar.FunctionalExtensionality.on;
//                  `%Interop.list_disjoint_or_eq;
//                  `%Interop.list_live
//                  ];
//      primops;
//      simplify]
//      x

// // Splitting the construction of the initial state into two functions
// // one that creates the initial trusted state (i.e., part of our TCB)
// // and another that just creates the vale state, a view upon the trusted one
// [@reduce]
// val create_initial_trusted_state_core
//        (acc:list b8)
//        (regs:registers)
//        (xmms:xmms_t)
//        (taint:taint_map)
//        (h0:HS.mem)
//        (stack:b8{mem_roots_p h0 (stack::acc)})
//   : GTot (TS.traceState & mem)

//   //This function folds over the `dom:list td`
// //and builds an arity-generic dependent function that constructs
// //the initial states
// //It's maybe more generic than it needs to be, since it is now applied only
// //once, i.e., with f = create_both_initial_states
// [@reduce]
// let rec create_initial_state_aux
//         #codom
//         (dom:list td)
//         (is_win:bool)
//         (i:nat{i + List.length dom < max_arity is_win})
//         (regs:registers)
//         (xmms:xmms_t)
//         (acc:list b8)
//         (taint:taint_map)
//         (f: (acc:list b8 -> registers -> xmms_t -> taint_map -> h:HS.mem -> stack:b8{mem_roots_p h (stack::acc)} -> GTot codom))
//       : n_dep_arrow
//         dom
//         (initial_state_t dom acc codom) =
//         match dom with
//         | [] ->
//           //no more args; build the state from a HS.mem
//           intro_dep_arrow_nil
//               (initial_state_t [] acc codom)
//               (f acc regs xmms taint)

//         | hd::tl ->
//           //put the next arg hd in the ith register
//           //update the taint map
//           //maybe add the next arg to the list of buffers
//           //recur
//           intro_dep_arrow_cons
//               hd
//               tl
//               (initial_state_t dom acc codom)
//               (fun (x:td_as_vale_type hd) ->
//                 fold_initial_state_t
//                   (create_initial_state_aux
//                     tl
//                     is_win
//                     (i + 1)
//                     (update_regs x is_win i regs)
//                     xmms
//                     (maybe_cons_buffer hd x acc)
//                     (update_taint_map x taint)
//                     f))

// let init_taint : taint_map = fun r -> Public

// let create_trusted_initial_state_t (dom:list td)
//                                 (acc:list b8)
//     = n_dep_arrow
//           dom
//           (initial_trusted_state_t dom acc)

// let create_trusted_initial_state
//       (is_win:bool)
//       (dom:list td{List.length dom < max_arity is_win})
//     : create_trusted_initial_state_t dom []
//     = create_initial_state_aux
//           dom
//           is_win
//           0
//           init_regs
//           init_xmms
//           []
//           init_taint
//           create_initial_trusted_state_core

// let stack_buffer = buffer64

// //////////////////////////////////////////////////////////////////////////////////////////
// //lowstar_sig:
// //    Interepreting an assembly language type as a Low* function type
// //////////////////////////////////////////////////////////////////////////////////////////

// let elim_down_1 (hd:td)
//                 (acc:list b8)
//                 (down:create_trusted_initial_state_t [hd] acc)
//                 (x:td_as_vale_type hd)
//     : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::maybe_cons_buffer hd x acc)} -> GTot (TS.traceState & mem) =
//     down x

// let elim_down_nil (acc:list b8)
//                   (down:create_trusted_initial_state_t [] acc)
//     : h0:HS.mem -> stack:b8{mem_roots_p h0 (stack::acc)} -> GTot (TS.traceState & mem) =
//     down

// let save_reg (r:reg) (s0 sN:TS.traceState) =
//   BS.eval_reg r s0.TS.state == BS.eval_reg r sN.TS.state

// let elim_down_cons (hd:td)
//                    (tl:list td)
//                    (acc:list b8)
//                    (down:create_trusted_initial_state_t (hd::tl) acc)
//                    (x:td_as_vale_type hd)
//     : create_trusted_initial_state_t tl (maybe_cons_buffer hd x acc) =
//     elim_dep_arrow_cons hd tl down x

// val prediction_pre
//     (c:code)
//     (acc:list b8)
//     (down:create_trusted_initial_state_t [] acc)
//     (h0:HS.mem)
//     (s0:TS.traceState)
//     (push_h0:mem_roots acc)
//     (alloc_push_h0:mem_roots acc)
//     (b:stack_buffer{mem_roots_p alloc_push_h0 ((to_b8 b)::acc)})
//     : Type0

// val prediction_post
//     (c:code)
//     (acc:list b8)
//     (down:create_trusted_initial_state_t [] acc)
//     (h0:HS.mem)
//     (s0:TS.traceState)
//     (push_h0:mem_roots acc)
//     (alloc_push_h0:mem_roots acc)
//     (b:stack_buffer{mem_roots_p alloc_push_h0 ((to_b8 b)::acc)})
//     (fuel_mem:nat & mem)
//     : Type0

// // (stack_bytes:nat)
// // stack_b:b8 ->
// let prediction (c:code) (acc:list b8) (down:create_trusted_initial_state_t [] acc) (h0:HS.mem) =
//   s0:TS.traceState ->
//   push_h0:mem_roots acc ->
//   alloc_push_h0:mem_roots acc ->
//   b:stack_buffer{mem_roots_p alloc_push_h0 ((to_b8 b)::acc)} ->
//   Ghost (nat & mem)
//     (requires prediction_pre c acc down h0 s0 push_h0 alloc_push_h0 b)
//     (ensures prediction_post c acc down h0 s0 push_h0 alloc_push_h0 b)

// noeq type as_lowstar_sig_ret (acc:list b8) =
//   | As_lowstar_sig_ret :
//       push_h0:mem_roots acc ->
//       alloc_push_h0:mem_roots acc ->
//       b:stack_buffer{mem_roots_p alloc_push_h0 ((to_b8 b)::acc)} ->
//       fuel:nat ->
//       final_mem:mem ->
//       as_lowstar_sig_ret acc

// val as_lowstar_sig_post
//     (c:code)
//     (acc:list b8)
//     (down:create_trusted_initial_state_t [] acc)
//     (h0:HS.mem)
//     (predict:prediction c acc down h0)
//     (push_h0:mem_roots acc)
//     (alloc_push_h0:mem_roots acc)
//     (b:stack_buffer{mem_roots_p alloc_push_h0 ((to_b8 b)::acc)})
//     (fuel:nat)
//     (final_mem:mem)
//     (h1:HS.mem)
//     : Type0

// let rec as_lowstar_sig_tl
//     (c:code)
//     (dom:list td)
//     (acc:list b8)
//     (down:create_trusted_initial_state_t dom acc)
//     : Type =
//     match dom with
//     | [] ->
//       h0:HS.mem ->
//       predict:prediction c acc down h0 ->
//       Stack (as_lowstar_sig_ret acc)
//         (requires (fun h0' -> h0 == h0' /\ mem_roots_p h0 acc))
//         (ensures fun h0 (As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem) h1 ->
//           as_lowstar_sig_post c acc down h0 predict push_h0 alloc_push_h0 b fuel final_mem h1
//         )
//     | hd::tl ->
//       x:td_as_vale_type hd ->
//       as_lowstar_sig_tl
//         c
//         tl
//         (maybe_cons_buffer hd x acc)
//         (elim_down_cons hd tl acc down x)

// let as_lowstar_sig (c:code) (dom:list td{List.length dom < max_arity win}) =
//     as_lowstar_sig_tl
//       c
//       dom
//       []
//       (create_trusted_initial_state win dom)

// val wrap (c:code) (dom:list td{List.length dom < max_arity win})
//   : as_lowstar_sig c dom
