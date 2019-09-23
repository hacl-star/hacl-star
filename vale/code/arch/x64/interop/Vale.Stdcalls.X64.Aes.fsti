module Vale.Stdcalls.X64.Aes

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open FStar.Mul

module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
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
open Vale.AES.AES_s

module AE = Vale.AES.X64.AES

let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
noextract
let as_t (#a:Type) (x:normal a) : a = x
noextract
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] noextract
let b128 = buf_t TUInt8 TUInt128
[@__reduce__] noextract
let t128_mod = TD_Buffer TUInt8 TUInt128 default_bq
[@__reduce__] noextract
let t128_no_mod = TD_Buffer TUInt8 TUInt128 ({modified=false; strict_disjointness=false; taint=MS.Secret})

[@__reduce__] noextract
let dom: IX64.arity_ok_stdcall td =
  let y = [t128_no_mod; t128_mod] in
  assert_norm (List.length y = 2);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let key128_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state) ->
      AE.va_req_KeyExpansionStdcall c va_s0 IA.win AES_128
        (as_vale_buffer input_b) (as_vale_buffer output_b)

[@__reduce__] noextract
let key128_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      AE.va_ens_KeyExpansionStdcall c va_s0 IA.win AES_128 (as_vale_buffer input_b) (as_vale_buffer output_b) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let key128_lemma'
    (code:V.va_code)
    (_win:bool)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       key128_pre code input_b output_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       key128_post code input_b output_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer input_b) /\
       ME.buffer_writeable (as_vale_buffer output_b)
 )) =
   let va_s1, f = AE.va_lemma_KeyExpansionStdcall code va_s0 IA.win AES_128
     (as_vale_buffer input_b) (as_vale_buffer output_b) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 input_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 output_b;
   (va_s1, f)

noextract
let key128_lemma = as_t #(VSig.vale_sig_stdcall key128_pre key128_post) key128_lemma'

noextract
let code_key128 = AE.va_code_KeyExpansionStdcall IA.win AES_128

[@__reduce__] noextract
let lowstar_key128_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_key128
    dom
    []
    _
    _
    (W.mk_prediction code_key128 dom [] (key128_lemma code_key128 IA.win))


(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let key256_pre : VSig.vale_pre dom =
  fun (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state) ->
      AE.va_req_KeyExpansionStdcall c va_s0 IA.win AES_256
        (as_vale_buffer input_b) (as_vale_buffer output_b)

[@__reduce__] noextract
let key256_post : VSig.vale_post dom =
  fun (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      AE.va_ens_KeyExpansionStdcall c va_s0 IA.win AES_256 (as_vale_buffer input_b) (as_vale_buffer output_b) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let key256_lemma'
    (code:V.va_code)
    (_win:bool)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       key256_pre code input_b output_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       key256_post code input_b output_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer input_b) /\
       ME.buffer_writeable (as_vale_buffer output_b)
 )) =
   let va_s1, f = AE.va_lemma_KeyExpansionStdcall code va_s0 IA.win AES_256
     (as_vale_buffer input_b) (as_vale_buffer output_b) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 input_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 output_b;
   (va_s1, f)

noextract
let key256_lemma = as_t #(VSig.vale_sig_stdcall key256_pre key256_post) key256_lemma'

noextract
let code_key256 = AE.va_code_KeyExpansionStdcall IA.win AES_256

[@__reduce__] noextract
let lowstar_key256_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_key256
    dom
    []
    _
    _
    (W.mk_prediction code_key256 dom [] (key256_lemma code_key256 IA.win))

[@ (CCConv "stdcall") ]
val aes128_key_expansion : normal lowstar_key128_t

[@ (CCConv "stdcall") ]
val aes256_key_expansion : normal lowstar_key256_t
