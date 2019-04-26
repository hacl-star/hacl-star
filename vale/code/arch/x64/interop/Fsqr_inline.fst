module Fsqr_inline

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
open Vale.AsLowStar.MemoryHelpers
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
let fsqr_dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; t64_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fsqr c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

let fsqr_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rbx || r = Rcx || r = Rdx || r = Rdi || r = Rsi || r = R8 || r = R9 || r = R10 || r = R11 || r = R12 || r = R13 || r = R14 || r = R15 then true
  else false

let fsqr_xmms_modified = fun _ -> false

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

[@__reduce__]
let fsqr_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr_pre code tmp f1 out va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fsqr_regs_modified fsqr_xmms_modified /\
       fsqr_post code tmp f1 out va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fsqr code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;   
   va_s1, f                                   

(* Prove that fsqr_lemma' has the required type *)
let fsqr_lemma = as_t #(VSig.vale_sig fsqr_regs_modified fsqr_xmms_modified fsqr_pre fsqr_post) fsqr_lemma'
let code_fsqr = FW.va_code_fsqr ()

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

(* Here's the type expected for the fsqr wrapper *)
[@__reduce__]
let lowstar_fsqr_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    Interop.down_mem
    code_fsqr
    fsqr_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

(* And here's the fsqr wrapper itself *)
let lowstar_fsqr : lowstar_fsqr_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    Interop.down_mem
    code_fsqr
    fsqr_dom
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

let lowstar_fsqr_normal_t : normal lowstar_fsqr_t
  = as_normal_t #lowstar_fsqr_t lowstar_fsqr

open Vale.AsLowStar.MemoryHelpers

let fsqr_inline tmp f1 out =
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview out);
    as_vale_buffer_len #TUInt64 #TUInt64 tmp;
    as_vale_buffer_len #TUInt64 #TUInt64 f1;
    as_vale_buffer_len #TUInt64 #TUInt64 out;    
    let x, _ = lowstar_fsqr_normal_t tmp f1 out () in
    ()

let fsqr_code_inline () : FStar.All.ML int =
  PR.print_inline "fsqr_inline" 0 None (List.length fsqr_dom) fsqr_dom code_fsqr of_arg fsqr_regs_modified

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr2_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fsqr2 c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr2_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr2 c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__]
let fsqr2_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr2_pre code tmp f1 out va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fsqr_regs_modified fsqr_xmms_modified /\
       fsqr2_post code tmp f1 out va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fsqr2 code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;    
   va_s1, f                                   

(* Prove that fsqr2_lemma' has the required type *)
let fsqr2_lemma = as_t #(VSig.vale_sig fsqr_regs_modified fsqr_xmms_modified fsqr2_pre fsqr2_post) fsqr2_lemma'
let code_fsqr2 = FW.va_code_fsqr2 ()

(* Here's the type expected for the fsqr2 wrapper *)
[@__reduce__]
let lowstar_fsqr2_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    Interop.down_mem
    code_fsqr2
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

(* And here's the fsqr2 wrapper itself *)
let lowstar_fsqr2 : lowstar_fsqr2_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    Interop.down_mem
    code_fsqr2
    fsqr_dom
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

let lowstar_fsqr2_normal_t : normal lowstar_fsqr2_t
  = as_normal_t #lowstar_fsqr2_t lowstar_fsqr2

open Vale.AsLowStar.MemoryHelpers

let fsqr2_inline tmp f1 out =
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview out);
    let x, _ = lowstar_fsqr2_normal_t tmp f1 out () in
    ()

let fsqr2_code_inline () : FStar.All.ML int =
  PR.print_inline "fsqr2_inline" 0 None (List.length fsqr_dom) fsqr_dom code_fsqr2 of_arg fsqr_regs_modified
