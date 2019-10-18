module Vale.Stdcalls.X64.AesHash

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

module GF = Vale.AES.X64.GF128_Init

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
let key128_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state) ->
      GF.va_req_Keyhash_init c va_s0 IA.win AES_128 (Ghost.reveal s)
        (as_vale_buffer input_b) (as_vale_buffer output_b)

[@__reduce__] noextract
let key128_post : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GF.va_ens_Keyhash_init c va_s0 IA.win AES_128 (Ghost.reveal s)
        (as_vale_buffer input_b) (as_vale_buffer output_b) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let key128_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       key128_pre s code input_b output_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       key128_post s code input_b output_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer input_b) /\
       ME.buffer_writeable (as_vale_buffer output_b)
 )) =
   let va_s1, f = GF.va_lemma_Keyhash_init code va_s0 IA.win AES_128 (Ghost.reveal s)
     (as_vale_buffer input_b) (as_vale_buffer output_b) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 input_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 output_b;
   (va_s1, f)

noextract
let key128_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (key128_pre s)  (key128_post s)) (key128_lemma' s)

noextract
let code_key128 = GF.va_code_Keyhash_init IA.win AES_128

[@__reduce__] noextract
let lowstar_key128_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_key128
    dom
    []
    _
    _
    (W.mk_prediction code_key128 dom [] ((key128_lemma s) code_key128 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_key128 (s:Ghost.erased (Seq.seq nat32)) : lowstar_key128_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_key128
    dom
    (W.mk_prediction code_key128 dom [] ((key128_lemma s) code_key128 IA.win))


(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let key256_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state) ->
      GF.va_req_Keyhash_init c va_s0 IA.win AES_256 (Ghost.reveal s)
        (as_vale_buffer input_b) (as_vale_buffer output_b)

[@__reduce__] noextract
let key256_post : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GF.va_ens_Keyhash_init c va_s0 IA.win AES_256 (Ghost.reveal s)
        (as_vale_buffer input_b) (as_vale_buffer output_b) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let key256_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (input_b:b128)
    (output_b:b128)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       key256_pre s code input_b output_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       key256_post s code input_b output_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer input_b) /\
       ME.buffer_writeable (as_vale_buffer output_b)
 )) =
   let va_s1, f = GF.va_lemma_Keyhash_init code va_s0 IA.win AES_256 (Ghost.reveal s)
     (as_vale_buffer input_b) (as_vale_buffer output_b) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 input_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 output_b;
   (va_s1, f)

noextract
let key256_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (key256_pre s)  (key256_post s)) (key256_lemma' s)

noextract
let code_key256 = GF.va_code_Keyhash_init IA.win AES_256

[@__reduce__] noextract
let lowstar_key256_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_key256
    dom
    []
    _
    _
    (W.mk_prediction code_key256 dom [] ((key256_lemma s) code_key256 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_key256 (s:Ghost.erased (Seq.seq nat32)) : lowstar_key256_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_key256
    dom
    (W.mk_prediction code_key256 dom [] ((key256_lemma s) code_key256 IA.win))


[@ (CCConv "stdcall") ]
let aes128_keyhash_init //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_key128_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_key128_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_key128 s)

[@ (CCConv "stdcall") ]
let aes256_keyhash_init //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_key256_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_key256_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_key256 s)
