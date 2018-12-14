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
module IM = Interop.Mem

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
let arity_ok 'a = l:list 'a { List.Tot.length l < max_arity }

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
  | TD_Base TUInt128 ->
     admit()
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

let arg_of_b8 (x:b8) : arg = (| TD_Buffer ME.TUInt8, x |)

let state_builder_t (args:list arg) (codom:Type) =
    h0:HS.mem ->
    stack:b8{mem_roots_p h0 (arg_of_b8 stack::args)} ->
    GTot codom

let init_taint : taint_map = fun r -> MS.Public

// Splitting the construction of the initial state into two functions
// one that creates the initial trusted state (i.e., part of our TCB)
// and another that just creates the vale state, a view upon the trusted one
let create_initial_trusted_state (args:arity_ok arg)
  : state_builder_t args (TS.traceState & ME.mem) =
  fun h0 stack ->
    let open MS in
    let regs = register_of_args (List.Tot.length args) args IA.init_regs in
    let regs = FunctionalExtensionality.on reg (regs_with_stack regs stack) in
    let xmms = FunctionalExtensionality.on xmm IA.init_xmms in
    let args = arg_of_b8 stack::args in
    Adapters.liveness_disjointness args h0;
    let mem:ME.mem = Adapters.mk_mem args h0 in
    let (s0:BS.state) = {
      BS.ok = true;
      BS.regs = regs;
      BS.xmms = xmms;
      BS.flags = 0;
      BS.mem = IM.down_mem h0 IA.addrs (Adapters.args_b8 args)
    } in
    {
      TS.state = s0;
      TS.trace = [];
      TS.memTaint = Adapters.create_valid_memtaint mem (Adapters.args_b8 args) init_taint
    },
    mem

////////////////////////////////////////////////////////////////////////////////
let stack_buffer = lowstar_buffer (ME.TBase ME.TUInt64)

let prediction_pre
    (c:TS.tainted_code)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (push_h0:mem_roots args)
    (alloc_push_h0:mem_roots args)
    (b:stack_buffer{mem_roots_p alloc_push_h0 (arg_of_b8 b::args)})
    =
  HS.fresh_frame h0 push_h0 /\
  B.modifies B.loc_none push_h0 alloc_push_h0 /\
  HS.get_tip push_h0 == HS.get_tip alloc_push_h0 /\
  B.frameOf b == HS.get_tip alloc_push_h0 /\
  B.live alloc_push_h0 b /\
  s0 == fst (create_initial_trusted_state args alloc_push_h0 b)

let prediction_post
    (c:TS.tainted_code)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (s0:TS.traceState)
    (push_h0:mem_roots args)
    (alloc_push_h0:mem_roots args)
    (b:stack_buffer{mem_roots_p alloc_push_h0 (arg_of_b8 b::args)})
    (rel: (nat & ME.mem) -> TS.traceState -> prop)
    (fuel_mem:nat & ME.mem) =
  let fuel, final_mem = fuel_mem in
  Some? (TS.taint_eval_code c fuel s0) /\ (
    let s1 = Some?.v (TS.taint_eval_code c fuel s0) in
    let h1 = Adapters.hs_of_mem final_mem in
    FStar.HyperStack.ST.equal_domains alloc_push_h0 h1 /\
    B.modifies (loc_args args) alloc_push_h0 h1 /\
    IM.down_mem h1 (IA.addrs)
                (Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem /\
    calling_conventions s0 s1 /\
    rel fuel_mem s1
  )

let prediction
    (c:TS.tainted_code)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (rel: (TS.traceState ->
           push_h0:mem_roots args ->
           alloc_push_h0:mem_roots args ->
           b:stack_buffer{mem_roots_p alloc_push_h0 (arg_of_b8 b::args)} ->
           (nat & ME.mem) ->
           TS.traceState ->
           prop)) =
  s0:TS.traceState ->
  push_h0:mem_roots args ->
  alloc_push_h0:mem_roots args ->
  b:stack_buffer{mem_roots_p alloc_push_h0 (arg_of_b8 b::args)} ->
  Ghost (nat & ME.mem)
    (requires prediction_pre c args h0 s0 push_h0 alloc_push_h0 b)
    (ensures prediction_post c args h0 s0 push_h0 alloc_push_h0 b (rel s0 push_h0 alloc_push_h0 b))

noeq type as_lowstar_sig_ret (args:arity_ok arg) =
  | As_lowstar_sig_ret :
      push_h0:mem_roots args ->
      alloc_push_h0:mem_roots args ->
      b:stack_buffer{mem_roots_p alloc_push_h0 (arg_of_b8 b::args)} ->
      fuel:nat ->
      final_mem:ME.mem ->
      as_lowstar_sig_ret args

let as_lowstar_sig_post
    (c:TS.tainted_code)
    (args:arity_ok arg)
    (h0:mem_roots args)
    (#rel: _)
    (predict:prediction c args h0 rel)
    (ret:as_lowstar_sig_ret args)
    (h1:HS.mem) =
  let As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem = ret in
  let s0 = fst (create_initial_trusted_state args alloc_push_h0 b) in
  let pre_pop = Adapters.hs_of_mem final_mem in
  prediction_pre c args h0 s0 push_h0 alloc_push_h0 b /\
  (fuel, final_mem) == predict s0 push_h0 alloc_push_h0 b /\
  FStar.HyperStack.ST.equal_domains alloc_push_h0 pre_pop /\
  HS.poppable pre_pop /\
  h1 == HS.pop pre_pop

let as_lowstar_sig (c:TS.tainted_code) =
    args:arity_ok arg ->
    h0:mem_roots args ->
    #rel:_ ->
    predict:prediction c args h0 rel ->
    FStar.HyperStack.ST.Stack (as_lowstar_sig_ret args)
        (requires (fun h0' -> h0 == h0' /\ mem_roots_p h0 args))
        (ensures fun h0 ret h1 -> as_lowstar_sig_post c args h0 #rel predict ret h1)

val wrap (c:TS.tainted_code) : as_lowstar_sig c
