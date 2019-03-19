module Vale.Stdcalls.Fsqr

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
noextract
let as_t (#a:Type) (x:normal a) : a = x
noextract
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] noextract
let b64 = buf_t TUInt64 TUInt64
[@__reduce__] noextract
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__] noextract
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] noextract
let tuint64 = TD_Base TUInt64

[@__reduce__] noextract
let fsqr_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let fsqr_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fsqr_stdcall c va_s0 IA.win
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__] noextract
let fsqr_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr_stdcall c va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__] noextract
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
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
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
   let va_s1, f = FW.va_lemma_fsqr_stdcall code va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;   
   va_s1, f                                   

(* Prove that fsqr_lemma' has the required type *)
noextract
let fsqr_lemma = as_t #(VSig.vale_sig_stdcall fsqr_pre fsqr_post) fsqr_lemma'
noextract
let code_fsqr = FW.va_code_fsqr_stdcall IA.win

(* Here's the type expected for the fsqr wrapper *)
[@__reduce__] noextract
let lowstar_fsqr_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_fsqr
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let fsqr2_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fsqr2_stdcall c va_s0 IA.win
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__] noextract
let fsqr2_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr2_stdcall c va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__] noextract
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
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
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
   let va_s1, f = FW.va_lemma_fsqr2_stdcall code va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;    
   va_s1, f                                   

(* Prove that fsqr2_lemma' has the required type *)
noextract
let fsqr2_lemma = as_t #(VSig.vale_sig_stdcall fsqr2_pre fsqr2_post) fsqr2_lemma'
noextract
let code_fsqr2 = FW.va_code_fsqr2_stdcall IA.win

(* Here's the type expected for the fsqr2 wrapper *)
[@__reduce__] noextract
let lowstar_fsqr2_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_fsqr2
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

[@ (CCConv "stdcall") ]
val fsqr : normal lowstar_fsqr_t

[@ (CCConv "stdcall") ]
val fsqr2 : normal lowstar_fsqr2_t
