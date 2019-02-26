module Fmul_inline

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

[@__reduce__] unfold
let b64 = buf_t TUInt64 TUInt64
[@__reduce__] unfold
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__] unfold
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] unfold
let tuint64 = TD_Base TUInt64

[@__reduce__] unfold
let fmul1_dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul1_pre : VSig.vale_pre 16 fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FH.va_req_fmul1 c va_s0 (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let fmul1_post : VSig.vale_post 16 fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fmul1 c va_s0 (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 50"

let fmul1_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rcx || r = Rdx || r = R8 || r = R9 || r = R10 || r = R11 || r = R12 || r = R13 then true
  else false

let fmul1_xmms_modified = fun _ -> false

[@__reduce__] unfold
let fmul1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul1_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fmul1_regs_modified fmul1_xmms_modified /\
       fmul1_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fmul1 code va_s0 (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that fmul1_lemma' has the required type *)
let fmul1_lemma = as_t #(VSig.vale_sig fmul1_regs_modified fmul1_xmms_modified fmul1_pre fmul1_post) fmul1_lemma'

let code_fmul1 = FH.va_code_fmul1 ()

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

(* Here's the type expected for the fmul1 wrapper *)
[@__reduce__]
let lowstar_fmul1_t =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fmul1_regs_modified
    fmul1_xmms_modified
    Interop.down_mem
    code_fmul1
    16
    fmul1_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_fmul1 fmul1_dom [] (fmul1_lemma code_fmul1 IA.win))

(* And here's the fmul1 wrapper itself *)
let lowstar_fmul1 : lowstar_fmul1_t  =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fmul1_regs_modified
    fmul1_xmms_modified
    Interop.down_mem
    code_fmul1
    16
    fmul1_dom
    (W.mk_prediction code_fmul1 fmul1_dom [] (fmul1_lemma code_fmul1 IA.win))

let lowstar_fmul1_normal_t : normal lowstar_fmul1_t
  = as_normal_t #lowstar_fmul1_t lowstar_fmul1

open Vale.AsLowStar.MemoryHelpers

let fmul1_inline out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    let x, _ = lowstar_fmul1_normal_t out f1 f2 () in
    ()

let fmul1_code_inline () : FStar.All.ML int =
  PR.print_inline "fmul1" 0 None (List.length fmul1_dom) fmul1_dom code_fmul1 of_arg fmul1_regs_modified
