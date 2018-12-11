module Interop.X64

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

////////////////////////////////////////////////////////////////////////////////
//The calling convention w.r.t the register mapping
////////////////////////////////////////////////////////////////////////////////

// Callee-saved registers that must be saved through an execution
let calling_conventions (s0:TS.traceState) (s1:TS.traceState) =
  let open MS in
  let s0 = s0.TS.state in
  let s1 = s1.TS.state in
  // Ensures that the execution didn't crash
  s1.BS.ok /\
  // Ensures that the callee_saved registers are correct
  (if IA.win then (
    // Calling conventions for Windows
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs Rdi == s1.BS.regs Rdi /\
    s0.BS.regs Rsi == s1.BS.regs Rsi /\
    s0.BS.regs Rsp == s1.BS.regs Rsp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15 /\
    s0.BS.xmms 6 == s1.BS.xmms 6 /\
    s0.BS.xmms 7 == s1.BS.xmms 7 /\
    s0.BS.xmms 8 == s1.BS.xmms 8 /\
    s0.BS.xmms 9 == s1.BS.xmms 9 /\
    s0.BS.xmms 10 == s1.BS.xmms 10 /\
    s0.BS.xmms 11 == s1.BS.xmms 11 /\
    s0.BS.xmms 12 == s1.BS.xmms 12 /\
    s0.BS.xmms 13 == s1.BS.xmms 13 /\
    s0.BS.xmms 14 == s1.BS.xmms 14 /\
    s0.BS.xmms 15 == s1.BS.xmms 15
  ) else (
    // Calling conventions for Linux
    s0.BS.regs Rbx == s1.BS.regs Rbx /\
    s0.BS.regs Rbp == s1.BS.regs Rbp /\
    s0.BS.regs R12 == s1.BS.regs R12 /\
    s0.BS.regs R13 == s1.BS.regs R13 /\
    s0.BS.regs R14 == s1.BS.regs R14 /\
    s0.BS.regs R15 == s1.BS.regs R15
    )
  )

let max_arity : nat = if IA.win then 4 else 6
let reg_nat = i:nat{i < max_arity}

[@reduce]
let register_of_arg_i (i:reg_nat) : MS.reg =
  let open MS in
  if IA.win then
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
[@reduce]
let arg_of_register (r:MS.reg)
  : option (i:reg_nat{register_of_arg_i i = r})
  = let open MS in
    if IA.win then
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

let registers = MS.reg -> MS.nat64

let upd_reg (regs:registers) (i:nat) (v:_) : registers =
    fun (r:MS.reg) ->
      match arg_of_register r with
      | Some j ->
        if i = j then v
        else regs r
      | _ -> regs r

[@reduce]
let arg_as_nat64 (a:arg) : GTot ME.nat64 =
  let (| tag, x |) = a in
  let open ME in
  match tag with
  | TD_Base TUInt8 ->
     UInt8.v x
  | TD_Base TUInt16 ->
     UInt16.v x
  | TD_Base TUInt32 ->
     UInt32.v x
  | TD_Base TUInt64 ->
     UInt64.v x
  | TD_Buffer bt ->
    IA.addrs x

[@reduce]
let update_regs (x:arg)
                (i:reg_nat)
                (regs:registers)
  : GTot registers
  = upd_reg regs i (arg_as_nat64 x)

let regs_with_stack (regs:registers) (stack_b:b8) : registers =
    fun r ->
      if r = MS.Rsp then
        IA.addrs stack_b
      else regs r

[@reduce]
let rec register_of_args (n:nat{n < max_arity})
                         (args:list arg{List.Tot.length args = n})
                         (regs:registers) : GTot registers =
    match args with
    | [] -> regs
    | hd::tl ->
      update_regs hd n (register_of_args (n - 1) tl regs)

////////////////////////////////////////////////////////////////////////////////
let taint_map = b8 -> GTot MS.taint

let upd_taint_map (taint:taint_map) (x:b8) : taint_map =
      fun (y:b8) ->
        if StrongExcludedMiddle.strong_excluded_middle ((x <: b8) == y) then
          MS.Secret
        else taint y

[@reduce]
let update_taint_map (#a:td)
                     (x:td_as_type a)
                     (taint:taint_map) =
    match a with
    | TD_Buffer bt ->
      upd_taint_map taint x
    | _ -> taint

////////////////////////////////////////////////////////////////////////////////

[@reduce]
let rec initial_state_t
              (dom:list td)
              (acc:list arg)
              (codom:Type)
  : n_arrow dom Type =
    match dom with
    | [] ->
      (h0:HS.mem ->
       stack:b8{mem_roots_p h0 ((|TD_Buffer ME.TUInt8, stack|)::acc)} ->
       GTot codom)
    | hd::tl ->
      fun (x:td_as_type hd) ->
         initial_state_t tl ((|hd, x|)::acc) codom

// Some identity coercions that serve as proof hints
// to introduce generic arrow types
[@reduce]
let fold_initial_state_t
  (#hd:td) (#tl:list td)
  (#x:td_as_type hd) (#acc:list arg) (#codom:Type)
  (res:n_dep_arrow tl (initial_state_t tl ((| hd, x |) :: acc) codom))
  : n_dep_arrow tl (elim_1 (initial_state_t (hd::tl) acc codom) x)
  = res

[@reduce]
let initial_trusted_state_t (dom:list td) (acc:list arg) =
  initial_state_t dom acc (TS.traceState & ME.mem)

// //This function folds over the `dom:list vale_type`
// //and builds an arity-generic dependent function that constructs
// //the initial states
// //It's maybe more generic than it needs to be, since it is now applied only
// //once, i.e., with f = create_both_initial_states
// [@reduce]
// let rec create_initial_state_aux
//         #codom
//         (args:list arg{List.Tot.length args < max_arity})
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
//               (fun (x:vale_type_as_type hd) ->
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
