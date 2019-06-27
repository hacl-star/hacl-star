module Vale.Stdcalls.X64.GCM_IV

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

module GC = Vale.AES.X64.GCMencryptOpt
open Vale.AES.GCM_s

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
let tuint64 = TD_Base TUInt64

[@__reduce__] noextract
let (dom: list td{List.length dom <= 20}) =
  let y = [t128_no_mod; tuint64; tuint64; t128_mod; t128_no_mod; t128_no_mod] in
  assert_norm (List.length y = 6);
  y


[@__reduce__] noextract
let compute_iv_pre : (Ghost.erased supported_iv_LE) -> VSig.vale_pre dom =
  fun (iv:Ghost.erased supported_iv_LE)
    (c:V.va_code)
    (iv_b:b128)
    (num_bytes:uint64)
    (len:uint64)
    (j0_b:b128)
    (iv_extra_b:b128)
    (hkeys_b:b128)
    (va_s0:V.va_state) ->
      GC.va_req_compute_iv_stdcall c va_s0 IA.win (Ghost.reveal iv)
        (as_vale_buffer iv_b) (UInt64.v num_bytes)
        (UInt64.v len) (as_vale_buffer j0_b)
        (as_vale_buffer iv_extra_b) (as_vale_buffer hkeys_b)

[@__reduce__] noextract
let compute_iv_post : (Ghost.erased supported_iv_LE) -> VSig.vale_post dom =
  fun (iv:Ghost.erased supported_iv_LE)
    (c:V.va_code)
    (iv_b:b128)
    (num_bytes:uint64)
    (len:uint64)
    (j0_b:b128)
    (iv_extra_b:b128)
    (hkeys_b:b128)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GC.va_ens_compute_iv_stdcall c va_s0 IA.win (Ghost.reveal iv)
        (as_vale_buffer iv_b) (UInt64.v num_bytes)
        (UInt64.v len) (as_vale_buffer j0_b)
        (as_vale_buffer iv_extra_b) (as_vale_buffer hkeys_b)
        va_s1 f

#set-options "--z3rlimit 50"

[@__reduce__] noextract
let compute_iv_lemma'
    (iv:Ghost.erased supported_iv_LE)
    (code:V.va_code)
    (_win:bool)
    (iv_b:b128)
    (num_bytes:uint64)
    (len:uint64)
    (j0_b:b128)
    (iv_extra_b:b128)
    (hkeys_b:b128)
    (va_s0:V.va_state)
  : Ghost (V.va_state & V.va_fuel)
    (requires compute_iv_pre iv code iv_b num_bytes len j0_b iv_extra_b hkeys_b va_s0)
    (ensures (fun (va_s1, f) ->
      V.eval_code code va_s0 f va_s1 /\
      VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
      compute_iv_post iv code iv_b num_bytes len j0_b iv_extra_b hkeys_b va_s0 va_s1 f /\      
      ME.buffer_writeable (as_vale_buffer iv_b) /\
      ME.buffer_writeable (as_vale_buffer hkeys_b) /\
      ME.buffer_writeable (as_vale_buffer iv_extra_b) /\
      ME.buffer_writeable (as_vale_buffer j0_b))
   ) = let va_s1, f = GC.va_lemma_compute_iv_stdcall code va_s0 IA.win (Ghost.reveal iv)
        (as_vale_buffer iv_b) (UInt64.v num_bytes)
        (UInt64.v len) (as_vale_buffer j0_b)
        (as_vale_buffer iv_extra_b) (as_vale_buffer hkeys_b) in
     Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 iv_b;
     Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 iv_extra_b;
     Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 j0_b; 
     Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 hkeys_b;
     va_s1, f

(* Prove that compute1_iv_lemma' has the required type *)
noextract
let compute_iv_lemma (iv:Ghost.erased supported_iv_LE) = as_t 
  #(VSig.vale_sig_stdcall (compute_iv_pre iv) (compute_iv_post iv))
   (compute_iv_lemma' iv)

noextract 
let code_compute_iv = GC.va_code_compute_iv_stdcall IA.win


(* Here's the type expected for the compute_iv wrapper *)
[@__reduce__] noextract
let lowstar_compute_iv_t (iv:Ghost.erased supported_iv_LE) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.as_lowstar_sig_t_weak_stdcall
    Vale.Interop.down_mem
    code_compute_iv
    dom
    []
    _
    _
    (W.mk_prediction code_compute_iv dom [] ((compute_iv_lemma iv) code_compute_iv IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_compute_iv (iv:Ghost.erased supported_iv_LE) : lowstar_compute_iv_t iv =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    Vale.Interop.down_mem
    code_compute_iv
    dom
    (W.mk_prediction code_compute_iv dom [] ((compute_iv_lemma iv) code_compute_iv IA.win))

[@ (CCConv "stdcall") ]
let compute_iv_stdcall
  = as_normal_t #((iv:Ghost.erased supported_iv_LE) -> lowstar_compute_iv_t iv) 
      (fun (iv:Ghost.erased supported_iv_LE) -> lowstar_compute_iv iv)
