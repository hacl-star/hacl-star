module Vale.Stdcalls.X64.Cpuid

open FStar.Mul
open Vale.Interop.Base
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module V = Vale.X64.Decls
module IA = Vale.Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters

module VC = Vale.Lib.X64.Cpuidstdcall

(* A little utility to trigger normalization in types *)
noextract
let as_t (#a:Type) (x:normal a) : a = x
noextract
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] noextract
let dom: IX64.arity_ok_stdcall td = []

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let aesni_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_aesni_stdcall c va_s0 IA.win

[@__reduce__] noextract
let aesni_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_aesni_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let aesni_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       aesni_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       aesni_post code va_s0 va_s1 f))
 = VC.va_lemma_check_aesni_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let aesni_lemma = as_t #(VSig.vale_sig_stdcall aesni_pre aesni_post) aesni_lemma'
noextract
let code_aesni = VC.va_code_check_aesni_stdcall IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__] noextract
let lowstar_aesni_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_aesni
    dom
    []
    _
    _
    (W.mk_prediction code_aesni dom [] (aesni_lemma code_aesni IA.win))


(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let sha_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_sha_stdcall c va_s0 IA.win

[@__reduce__] noextract
let sha_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_sha_stdcall c va_s0 IA.win va_s1 f

open Vale.X64.Machine_s
open Vale.X64.State

#set-options "--z3rlimit 20"

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let sha_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       sha_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       sha_post code va_s0 va_s1 f))
 = VC.va_lemma_check_sha_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let sha_lemma = as_t #(VSig.vale_sig_stdcall sha_pre sha_post) sha_lemma'
noextract
let code_sha = VC.va_code_check_sha_stdcall IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__] noextract
let lowstar_sha_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_sha
    dom
    []
    _
    _
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))


(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let adx_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_adx_bmi2_stdcall c va_s0 IA.win

[@__reduce__] noextract
let adx_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_adx_bmi2_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let adx_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       adx_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       adx_post code va_s0 va_s1 f))
 = VC.va_lemma_check_adx_bmi2_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let adx_lemma = as_t #(VSig.vale_sig_stdcall adx_pre adx_post) adx_lemma'
noextract
let code_adx = VC.va_code_check_adx_bmi2_stdcall IA.win

(* Here's the type expected for the check_adx wrapper *)
[@__reduce__] noextract
let lowstar_adx_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_adx
    dom
    []
    _
    _
    (W.mk_prediction code_adx dom [] (adx_lemma code_adx IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let avx_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_avx_stdcall c va_s0 IA.win

[@__reduce__] noextract
let avx_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_avx_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let avx_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       avx_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       avx_post code va_s0 va_s1 f))
 = VC.va_lemma_check_avx_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let avx_lemma = as_t #(VSig.vale_sig_stdcall avx_pre avx_post) avx_lemma'
noextract
let code_avx = VC.va_code_check_avx_stdcall IA.win

(* Here's the type expected for the check_avx wrapper *)
[@__reduce__] noextract
let lowstar_avx_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_avx
    dom
    []
    _
    _
    (W.mk_prediction code_avx dom [] (avx_lemma code_avx IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let avx2_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_avx2_stdcall c va_s0 IA.win

[@__reduce__] noextract
let avx2_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_avx2_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let avx2_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       avx2_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       avx2_post code va_s0 va_s1 f))
 = VC.va_lemma_check_avx2_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let avx2_lemma = as_t #(VSig.vale_sig_stdcall avx2_pre avx2_post) avx2_lemma'
noextract
let code_avx2 = VC.va_code_check_avx2_stdcall IA.win

(* Here's the type expected for the check_avx wrapper *)
[@__reduce__] noextract
let lowstar_avx2_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_avx2
    dom
    []
    _
    _
    (W.mk_prediction code_avx2 dom [] (avx2_lemma code_avx2 IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let movbe_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_movbe_stdcall c va_s0 IA.win

[@__reduce__] noextract
let movbe_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_movbe_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let movbe_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       movbe_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       movbe_post code va_s0 va_s1 f))
 = VC.va_lemma_check_movbe_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let movbe_lemma = as_t #(VSig.vale_sig_stdcall movbe_pre movbe_post) movbe_lemma'
noextract
let code_movbe = VC.va_code_check_movbe_stdcall IA.win

(* Here's the type expected for the check_movbe wrapper *)
[@__reduce__] noextract
let lowstar_movbe_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_movbe
    dom
    []
    _
    _
    (W.mk_prediction code_movbe dom [] (movbe_lemma code_movbe IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let sse_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_sse_stdcall c va_s0 IA.win

[@__reduce__] noextract
let sse_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_sse_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let sse_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       sse_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       sse_post code va_s0 va_s1 f))
 = VC.va_lemma_check_sse_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let sse_lemma = as_t #(VSig.vale_sig_stdcall sse_pre sse_post) sse_lemma'
noextract
let code_sse = VC.va_code_check_sse_stdcall IA.win

(* Here's the type expected for the check_sse wrapper *)
[@__reduce__] noextract
let lowstar_sse_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_sse
    dom
    []
    _
    _
    (W.mk_prediction code_sse dom [] (sse_lemma code_sse IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let rdrand_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_check_rdrand_stdcall c va_s0 IA.win

[@__reduce__] noextract
let rdrand_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_check_rdrand_stdcall c va_s0 IA.win va_s1 f

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__] noextract
let rdrand_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       rdrand_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       rdrand_post code va_s0 va_s1 f))
 = VC.va_lemma_check_rdrand_stdcall code va_s0 IA.win

(* Prove that vm_lemma' has the required type *)
noextract
let rdrand_lemma = as_t #(VSig.vale_sig_stdcall rdrand_pre rdrand_post) rdrand_lemma'
noextract
let code_rdrand = VC.va_code_check_rdrand_stdcall IA.win

(* Here's the type expected for the check_rdrand wrapper *)
[@__reduce__] noextract
let lowstar_rdrand_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_rdrand
    dom
    []
    _
    _
    (W.mk_prediction code_rdrand dom [] (rdrand_lemma code_rdrand IA.win))

[@ (CCConv "stdcall") ]
val check_aesni : normal lowstar_aesni_t

[@ (CCConv "stdcall") ]
val check_sha : normal lowstar_sha_t

[@ (CCConv "stdcall") ]
val check_adx_bmi2 : normal lowstar_adx_t

[@ (CCConv "stdcall") ]
val check_avx : normal lowstar_avx_t

[@ (CCConv "stdcall") ]
val check_avx2 : normal lowstar_avx2_t

[@ (CCConv "stdcall") ]
val check_movbe : normal lowstar_movbe_t

[@ (CCConv "stdcall") ]
val check_sse : normal lowstar_sse_t

[@ (CCConv "stdcall") ]
val check_rdrand : normal lowstar_rdrand_t
