module Vale.Stdcalls.X64.Poly
open FStar.Mul

val z3rlimit_hack (x:nat) : squash (x < x + x + 1)
#reset-options "--z3rlimit 50"

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module DV = LowStar.BufferView.Down
open Vale.Def.Types_s

open Vale.Interop.Base
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module ME = Vale.X64.Memory
module V = Vale.X64.Decls
module IA = Vale.Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters
module VS = Vale.X64.State
module MS = Vale.X64.Machine_s

module PO = Vale.Poly1305.X64
open Vale.Poly1305.Math

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
  let y = [t64_mod; t64_no_mod; tuint64; tuint64] in
  assert_norm (List.length y = 4);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let poly_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (finish:uint64)
    (va_s0:V.va_state) ->
      PO.va_req_Poly1305 c va_s0 IA.win
        (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len) (UInt64.v finish)

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let poly_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (finish:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      PO.va_ens_Poly1305 c va_s0 IA.win
        (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len) (UInt64.v finish)
        va_s1 f

module VS = Vale.X64.State

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let poly_lemma'
    (code:V.va_code)
    (_win:bool)
    (ctx_b:b64)
    (inp_b:b64)
    (len:uint64)
    (finish:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       poly_pre code ctx_b inp_b len finish va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       poly_post code ctx_b inp_b len finish va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer ctx_b) /\
       ME.buffer_writeable (as_vale_buffer inp_b)
 )) =
   let va_s1, f = PO.va_lemma_Poly1305 code va_s0 IA.win (as_vale_buffer ctx_b) (as_vale_buffer inp_b) (UInt64.v len) (UInt64.v finish) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt64 ctx_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt64 inp_b;
   va_s1, f

(* Prove that poly_lemma' has the required type *)
noextract
let poly_lemma = as_t #(VSig.vale_sig_stdcall poly_pre poly_post) poly_lemma'
noextract
let code_poly = PO.va_code_Poly1305 IA.win

(* Here's the type expected for the poly wrapper *)
[@__reduce__] noextract
let lowstar_poly_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_poly
    dom
    []
    _
    _
    (W.mk_prediction code_poly dom [] (poly_lemma code_poly IA.win))

[@ (CCConv "stdcall") ]
val x64_poly1305 : normal lowstar_poly_t
