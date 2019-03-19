module Fswap_inline

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
let cswap_dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let cswap_pre : VSig.vale_pre cswap_dom =
  fun (c:V.va_code)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state) ->
      FU.va_req_cswap2 c va_s0
        (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit)

[@__reduce__]
let cswap_post : VSig.vale_post cswap_dom =
  fun (c:V.va_code)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_cswap2 c va_s0 (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit) va_s1 f

#set-options "--z3rlimit 50"

let cswap_regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rdx || r = R8 || r = R9 || r = R10 then true
  else false

let cswap_xmms_modified = fun _ -> false

[@__reduce__]
let cswap_lemma'
    (code:V.va_code)
    (_win:bool)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       cswap_pre code p0 p1 bit va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 cswap_regs_modified cswap_xmms_modified /\
       cswap_post code p0 p1 bit va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer p0) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer p1) /\ 
       ME.buffer_writeable (as_vale_buffer p0) /\ 
       ME.buffer_writeable (as_vale_buffer p1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer p0))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer p1))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_cswap2 code va_s0 (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 p0;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 p1;   
   va_s1, f                                   

(* Prove that cswap_lemma' has the required type *)
let cswap_lemma = as_t #(VSig.vale_sig cswap_regs_modified cswap_xmms_modified cswap_pre cswap_post) cswap_lemma'

let code_cswap = FU.va_code_cswap2 ()

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

(* Here's the type expected for the cswap wrapper *)
[@__reduce__]
let lowstar_cswap_t =
  assert_norm (List.length cswap_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    cswap_regs_modified
    cswap_xmms_modified
    Interop.down_mem
    code_cswap
    cswap_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

(* And here's the cswap wrapper itself *)
let lowstar_cswap : lowstar_cswap_t  =
  assert_norm (List.length cswap_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    cswap_regs_modified
    cswap_xmms_modified
    Interop.down_mem
    code_cswap
    cswap_dom
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

let lowstar_cswap_normal_t : normal lowstar_cswap_t
  = as_normal_t #lowstar_cswap_t lowstar_cswap

open Vale.AsLowStar.MemoryHelpers

let cswap2_inline p0 p1 bit
  = DV.length_eq (get_downview p0);
    DV.length_eq (get_downview p1);
    let x, _ = lowstar_cswap_normal_t p0 p1 bit () in
    ()

let cswap2_code_inline () : FStar.All.ML int =
  PR.print_inline "cswap2_inline" 0 None (List.length cswap_dom) cswap_dom code_cswap of_arg cswap_regs_modified
