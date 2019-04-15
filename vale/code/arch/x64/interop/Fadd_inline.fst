module Fadd_inline

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
open Types_s

open Interop.Base
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module ME = X64.Memory
module V = X64.Vale.Decls
module IA = Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open X64.MemoryAdapters
module VS = X64.Vale.State
module MS = X64.Machine_s
module PR = X64.Print_Inline_s

module FU = X64.FastUtil
module FH = X64.FastHybrid
module FW = X64.FastWide

let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__]
let b64 = buf_t TUInt64 TUInt64
[@__reduce__]
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__]
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__]
let tuint64 = TD_Base TUInt64

[@__reduce__]
let dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let add1_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state) ->
      FU.va_req_fast_add1 c va_s0
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let add1_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_fast_add1 c va_s0 (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 50"

let add1_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rdx || r = R8 || r = R9 || r = R10 || r = R11 then true
  else false

let add1_xmms_modified = fun _ -> false

[@__reduce__]
let add1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       add1_pre code out f1 f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 add1_regs_modified add1_xmms_modified /\
       add1_post code out f1 f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_fast_add1 code va_s0 (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let add1_lemma = as_t #(VSig.vale_sig add1_regs_modified add1_xmms_modified add1_pre add1_post) add1_lemma'

let code_add1 = FU.va_code_fast_add1 ()

let of_reg (r:MS.reg) : option (IX64.reg_nat 3) = match r with
  | MS.Rdi -> Some 0
  | MS.Rsi -> Some 1
  | MS.Rdx -> Some 2
  | _ -> None

let of_arg (i:IX64.reg_nat 3) = match i with
  | 0 -> MS.Rdi
  | 1 -> MS.Rsi
  | 2 -> MS.Rdx

let arg_reg : IX64.arg_reg_relation 3 = IX64.Rel of_reg of_arg

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_add1_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    add1_regs_modified
    add1_xmms_modified
    Interop.down_mem
    code_add1
    dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

(* And here's the add1 wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    add1_regs_modified
    add1_xmms_modified
    Interop.down_mem
    code_add1
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

let lowstar_add1_normal_t : normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

open Vale.AsLowStar.MemoryHelpers

let add1_inline out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    let x, _ = lowstar_add1_normal_t out f1 f2 () in
    x

let add1_code_inline () : FStar.All.ML int =
  PR.print_inline "add1_inline" 0 (Some "carry_r") (List.length dom) dom code_add1 of_arg add1_regs_modified


[@__reduce__]
let fadd_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_no_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fadd_pre : VSig.vale_pre fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state) ->
      FH.va_req_fadd c va_s0
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fadd_post : VSig.vale_post fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fadd c va_s0 (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 50"

let fadd_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rcx || r = Rdx || r = R8 || r = R9 || r = R10 || r = R11 then true
  else false

let fadd_xmms_modified = fun _ -> false

[@__reduce__]
let fadd_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fadd_pre code out f1 f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fadd_regs_modified fadd_xmms_modified /\
       fadd_post code out f1 f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fadd code va_s0 (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let fadd_lemma = as_t #(VSig.vale_sig fadd_regs_modified fadd_xmms_modified fadd_pre fadd_post) fadd_lemma'

let code_fadd = FH.va_code_fadd ()

(* Here's the type expected for the fadd wrapper *)
[@__reduce__]
let lowstar_fadd_t =
  assert_norm (List.length fadd_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fadd_regs_modified
    fadd_xmms_modified
    Interop.down_mem
    code_fadd
    fadd_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

(* And here's the fadd wrapper itself *)
let lowstar_fadd : lowstar_fadd_t  =
  assert_norm (List.length fadd_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fadd_regs_modified
    fadd_xmms_modified
    Interop.down_mem
    code_fadd
    fadd_dom
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

let lowstar_fadd_normal_t : normal lowstar_fadd_t
  = as_normal_t #lowstar_fadd_t lowstar_fadd

let fadd_inline out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview f2);
    let x, _ = lowstar_fadd_normal_t out f1 f2 () in
    ()

let fadd_code_inline () : FStar.All.ML int =
  PR.print_inline "fadd_inline" 0 None (List.length fadd_dom) fadd_dom code_fadd of_arg fadd_regs_modified

[@__reduce__]
let fsub_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_no_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsub_pre : VSig.vale_pre fsub_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state) ->
      FH.va_req_fsub c va_s0
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fsub_post : VSig.vale_post fsub_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fsub c va_s0 (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 50"

let fsub_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rcx || r = R8 || r = R9 || r = R10 || r = R11 then true
  else false

let fsub_xmms_modified = fun _ -> false

[@__reduce__]
let fsub_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsub_pre code out f1 f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fsub_regs_modified fsub_xmms_modified /\
       fsub_post code out f1 f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fsub code va_s0 (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that fsub_lemma' has the required type *)
let fsub_lemma = as_t #(VSig.vale_sig fsub_regs_modified fsub_xmms_modified fsub_pre fsub_post) fsub_lemma'

let code_fsub = FH.va_code_fsub ()

(* Here's the type expected for the fsub wrapper *)
[@__reduce__]
let lowstar_fsub_t =
  assert_norm (List.length fsub_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fsub_regs_modified
    fsub_xmms_modified
    Interop.down_mem
    code_fsub
    fsub_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_fsub fsub_dom [] (fsub_lemma code_fsub IA.win))

(* And here's the fsub wrapper itself *)
let lowstar_fsub : lowstar_fsub_t  =
  assert_norm (List.length fsub_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fsub_regs_modified
    fsub_xmms_modified
    Interop.down_mem
    code_fsub
    fsub_dom
    (W.mk_prediction code_fsub fsub_dom [] (fsub_lemma code_fsub IA.win))

let lowstar_fsub_normal_t : normal lowstar_fsub_t
  = as_normal_t #lowstar_fsub_t lowstar_fsub

let fsub_inline out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview f2);
    let x, _ = lowstar_fsub_normal_t out f1 f2 () in
    ()

let fsub_code_inline () : FStar.All.ML int =
  PR.print_inline "fsub_inline" 0 None (List.length fsub_dom) fsub_dom code_fsub of_arg fsub_regs_modified
