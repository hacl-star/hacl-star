module Cpuid_stdcalls
open Interop.Base
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module V = X64.Vale.Decls
module IA = Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open X64.MemoryAdapters

module VC = X64.Cpuidstdcall

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__]
let dom: IX64.arity_ok_stdcall td = []

(* Need to rearrange the order of arguments *)
[@__reduce__]
let aesni_pre : VSig.vale_pre 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8) ->
      VC.va_req_check_aesni_stdcall c va_s0 IA.win (as_vale_buffer sb)

[@__reduce__]
let aesni_post : VSig.vale_post 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_aesni_stdcall c va_s0 IA.win (as_vale_buffer sb) va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] unfold
let aesni_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       aesni_pre code va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       aesni_post code va_s0 sb va_s1 f))
 = VC.va_lemma_check_aesni_stdcall code va_s0 IA.win (as_vale_buffer sb)

(* Prove that vm_lemma' has the required type *)
let aesni_lemma = as_t #(VSig.vale_sig aesni_pre aesni_post) aesni_lemma'
let code_aesni = VC.va_code_check_aesni_stdcall IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__]
let lowstar_aesni_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_aesni
    8
    dom
    []
    _
    _
    (W.mk_prediction code_aesni dom [] (aesni_lemma code_aesni IA.win))

(* And here's the check_aesni wrapper itself *)
let lowstar_aesni : lowstar_aesni_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_aesni
    8
    dom
    (W.mk_prediction code_aesni dom [] (aesni_lemma code_aesni IA.win))

let lowstar_aesni_normal_t //: normal lowstar_aesni_t
  = as_normal_t #lowstar_aesni_t lowstar_aesni

let check_aesni () =  
  let x, _ = lowstar_aesni_normal_t () in //This is a call to the interop wrapper
  x

(* Need to rearrange the order of arguments *)
[@__reduce__]
let sha_pre : VSig.vale_pre 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8) ->
      VC.va_req_check_sha_stdcall c va_s0 IA.win (as_vale_buffer sb)

[@__reduce__]
let sha_post : VSig.vale_post 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_sha_stdcall c va_s0 IA.win (as_vale_buffer sb) va_s1 f

open X64.Machine_s
open X64.Vale.State

#set-options "--z3rlimit 20"

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] unfold
let sha_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       sha_pre code va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       sha_post code va_s0 sb va_s1 f))
 = VC.va_lemma_check_sha_stdcall code va_s0 IA.win (as_vale_buffer sb)
 
(* Prove that vm_lemma' has the required type *)
let sha_lemma = as_t #(VSig.vale_sig sha_pre sha_post) sha_lemma'
let code_sha = VC.va_code_check_sha_stdcall IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__]
let lowstar_sha_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_sha
    8
    dom
    []
    _
    _
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

(* And here's the check_aesni wrapper itself *)
let lowstar_sha : lowstar_sha_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_sha
    8
    dom
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

let lowstar_sha_normal_t //: normal lowstar_sha_t
  = as_normal_t #lowstar_sha_t lowstar_sha

let check_sha () =  
  let x, _ = lowstar_sha_normal_t () in //This is a call to the interop wrapper
  x

(* Need to rearrange the order of arguments *)
[@__reduce__]
let adx_pre : VSig.vale_pre 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8) ->
      VC.va_req_check_adx_bmi2_stdcall c va_s0 IA.win (as_vale_buffer sb)

[@__reduce__]
let adx_post : VSig.vale_post 8 dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_adx_bmi2_stdcall c va_s0 IA.win (as_vale_buffer sb) va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] unfold
let adx_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 8)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       adx_pre code va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       adx_post code va_s0 sb va_s1 f))
 = VC.va_lemma_check_adx_bmi2_stdcall code va_s0 IA.win (as_vale_buffer sb)

(* Prove that vm_lemma' has the required type *)
let adx_lemma = as_t #(VSig.vale_sig adx_pre adx_post) adx_lemma'
let code_adx = VC.va_code_check_adx_bmi2_stdcall IA.win

(* Here's the type expected for the check_adx wrapper *)
[@__reduce__]
let lowstar_adx_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_adx
    8
    dom
    []
    _
    _
    (W.mk_prediction code_adx dom [] (adx_lemma code_adx IA.win))

(* And here's the check_adx wrapper itself *)
let lowstar_adx : lowstar_adx_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_adx
    8
    dom
    (W.mk_prediction code_adx dom [] (adx_lemma code_adx IA.win))

let lowstar_adx_normal_t //: normal lowstar_adx_t
  = as_normal_t #lowstar_adx_t lowstar_adx

let check_adx_bmi2 () =  
  let x, _ = lowstar_adx_normal_t () in //This is a call to the interop wrapper
  x
