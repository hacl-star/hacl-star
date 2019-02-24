module Fsub_stdcalls

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
let dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_no_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsub_pre : VSig.vale_pre 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FH.va_req_fsub_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fsub_post : VSig.vale_post 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fsub_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fsub_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsub_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       fsub_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fsub_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that fsub_lemma' has the required type *)
let fsub_lemma = as_t #(VSig.vale_sig_stdcall fsub_pre fsub_post) fsub_lemma'

let code_fsub = FH.va_code_fsub_stdcall IA.win

(* Here's the type expected for the fsub wrapper *)
[@__reduce__]
let lowstar_fsub_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_fsub
    16
    dom
    []
    _
    _
    (W.mk_prediction code_fsub dom [] (fsub_lemma code_fsub IA.win))

(* And here's the fsub wrapper itself *)
let lowstar_fsub : lowstar_fsub_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fsub
    16
    dom
    (W.mk_prediction code_fsub dom [] (fsub_lemma code_fsub IA.win))

let lowstar_fsub_normal_t //: normal lowstar_fsub_t
  = as_normal_t #lowstar_fsub_t lowstar_fsub

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsub out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let x, _ = lowstar_fsub_normal_t out f1 f2 () in
  ()

#pop-options
