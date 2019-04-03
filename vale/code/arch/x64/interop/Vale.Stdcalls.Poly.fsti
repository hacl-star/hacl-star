module Vale.Stdcalls.Poly

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
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

module PO = X64.Poly1305
open X64.Poly1305.Math

let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
noextract
let as_t (#a:Type) (x:normal a) : a = x
noextract
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] noextract
let b64 = buf_t TUInt8 TUInt64
[@__reduce__] noextract
let t64_mod = TD_Buffer TUInt8 TUInt64 ({modified=true; strict_disjointness=false; taint=MS.Public})
[@__reduce__] noextract
let t64_no_mod = TD_Buffer TUInt8 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Public})
[@__reduce__] noextract
let tuint64 = TD_Base TUInt64

[@__reduce__] noextract
let dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let poly_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (va_s0:V.va_state) ->
      PO.va_req_poly1305 c va_s0 IA.win
        (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len)

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let poly_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      PO.va_ens_poly1305 c va_s0 IA.win
        (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len)
        va_s1 f

module VS = X64.Vale.State

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let poly_lemma'
    (code:V.va_code)
    (_win:bool)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       poly_pre code ctx_b inp_b len va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       poly_post code ctx_b inp_b len va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer ctx_b) /\ 
       ME.buffer_writeable (as_vale_buffer inp_b) 
 )) = 
   let va_s1, f = PO.va_lemma_poly1305 code va_s0 IA.win (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt64 ctx_b;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt64 inp_b;   
   va_s1, f

(* Prove that poly_lemma' has the required type *)
noextract
let poly_lemma = as_t #(VSig.vale_sig_stdcall poly_pre poly_post) poly_lemma'
noextract
let code_poly = PO.va_code_poly1305 IA.win

(* Here's the type expected for the poly wrapper *)
[@__reduce__] noextract
let lowstar_poly_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_poly
    dom
    []
    _
    _
    (W.mk_prediction code_poly dom [] (poly_lemma code_poly IA.win))

[@ (CCConv "stdcall") ]
val poly1305 : normal lowstar_poly_t
