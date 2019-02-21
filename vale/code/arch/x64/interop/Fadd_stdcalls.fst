module Fadd_stdcalls

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
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

module FU = X64.FastUtil
module FH = X64.FastHybrid
module FW = X64.FastWide

let b8 = B.buffer UInt8.t
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
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let add1_pre : VSig.vale_pre 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FU.va_req_fast_add1_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let add1_post : VSig.vale_post 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_fast_add1_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

module VS = X64.Vale.State

#set-options "--z3rlimit 20"

[@__reduce__] unfold
let add1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       add1_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       add1_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_fast_add1_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let add1_lemma = as_t #(VSig.vale_sig_stdcall add1_pre add1_post) add1_lemma'

let code_add1 = FU.va_code_fast_add1_stdcall IA.win

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_add1_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_add1
    16
    dom
    []
    _
    _
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

(* And here's the add1 wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_add1
    16
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

// TODO: This as  separate module extracted by KreMLin

let lowstar_add1_normal_t : normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

open Vale.AsLowStar.MemoryHelpers

#set-options "--z3rlimit 50"

// TODO: This inlined, and just extracted regularly (no -library)

let add1 out f1 f2 =
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview out);
  let x, _ = lowstar_add1_normal_t out f1 f2 () in
  x


[@__reduce__] unfold
let fadd_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_no_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fadd_pre : VSig.vale_pre 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FH.va_req_fadd_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fadd_post : VSig.vale_post 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fadd_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fadd_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fadd_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       fadd_post code out f1 f2 va_s0 sb va_s1 f /\
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
   let va_s1, f = FH.va_lemma_fadd_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let fadd_lemma = as_t #(VSig.vale_sig_stdcall fadd_pre fadd_post) fadd_lemma'

let code_fadd = FH.va_code_fadd_stdcall IA.win

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_fadd_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_fadd
    16
    fadd_dom
    []
    _
    _
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

(* And here's the fadd wrapper itself *)
let lowstar_fadd : lowstar_fadd_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fadd
    16
    fadd_dom
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

let lowstar_fadd_normal_t //: normal lowstar_add1_t
  = as_normal_t #lowstar_fadd_t lowstar_fadd

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fadd out f1 f2 =
  DV.length_eq (get_downview out);
  DV.length_eq (get_downview f1);
  DV.length_eq (get_downview f2);
  let x, _ = lowstar_fadd_normal_t out f1 f2 () in
  ()
  
#pop-options
