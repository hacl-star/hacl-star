module Vale.Stdcalls.X64.GCTR

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

module GC = Vale.AES.X64.GCTR

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
  let y = [t128_no_mod; tuint64; t128_mod; t128_mod; t128_no_mod; t128_no_mod; tuint64] in
  assert_norm (List.length y = 7);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gctr128_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state) ->
      GC.va_req_Gctr_bytes_stdcall c va_s0 IA.win AES_128
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s)

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gctr128_post : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GC.va_ens_Gctr_bytes_stdcall c va_s0 IA.win AES_128
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let gctr128_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       gctr128_pre s code in_b num_bytes out_b inout_b keys_b ctr_b num_blocks va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       gctr128_post s code in_b num_bytes out_b inout_b keys_b ctr_b num_blocks va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer in_b) /\
       ME.buffer_writeable (as_vale_buffer keys_b) /\
       ME.buffer_writeable (as_vale_buffer ctr_b) /\
       ME.buffer_writeable (as_vale_buffer inout_b) /\
       ME.buffer_writeable (as_vale_buffer out_b)
 )) =
   let va_s1, f = GC.va_lemma_Gctr_bytes_stdcall code va_s0 IA.win AES_128
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 inout_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 keys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 ctr_b;
   (va_s1, f)

noextract
let gctr128_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (gctr128_pre s)  (gctr128_post s)) (gctr128_lemma' s)

noextract
let code_gctr128 = GC.va_code_Gctr_bytes_stdcall IA.win AES_128

[@__reduce__] noextract
let lowstar_gctr128_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_gctr128
    dom
    []
    _
    _
    (W.mk_prediction code_gctr128 dom [] ((gctr128_lemma s) code_gctr128 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_gctr128 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gctr128_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    code_gctr128
    dom
    (W.mk_prediction code_gctr128 dom [] ((gctr128_lemma s) code_gctr128 IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gctr256_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state) ->
      GC.va_req_Gctr_bytes_stdcall c va_s0 IA.win AES_256
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s)

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gctr256_post : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GC.va_ens_Gctr_bytes_stdcall c va_s0 IA.win AES_256
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let gctr256_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (in_b:b128)
    (num_bytes:uint64)
    (out_b:b128)
    (inout_b:b128)
    (keys_b:b128)
    (ctr_b:b128)
    (num_blocks:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       gctr256_pre s code in_b num_bytes out_b inout_b keys_b ctr_b num_blocks va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       gctr256_post s code in_b num_bytes out_b inout_b keys_b ctr_b num_blocks va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer in_b) /\
       ME.buffer_writeable (as_vale_buffer keys_b) /\
       ME.buffer_writeable (as_vale_buffer ctr_b) /\
       ME.buffer_writeable (as_vale_buffer inout_b) /\
       ME.buffer_writeable (as_vale_buffer out_b)
 )) =
   let va_s1, f = GC.va_lemma_Gctr_bytes_stdcall code va_s0 IA.win AES_256
        (as_vale_buffer in_b) (UInt64.v num_bytes)
        (as_vale_buffer out_b) (as_vale_buffer inout_b) (as_vale_buffer keys_b)
        (as_vale_buffer ctr_b) (UInt64.v num_blocks) (Ghost.reveal s) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 inout_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 keys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 ctr_b;
   (va_s1, f)

noextract
let gctr256_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (gctr256_pre s)  (gctr256_post s)) (gctr256_lemma' s)

noextract
let code_gctr256 = GC.va_code_Gctr_bytes_stdcall IA.win AES_256

[@__reduce__] noextract
let lowstar_gctr256_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_gctr256
    dom
    []
    _
    _
    (W.mk_prediction code_gctr256 dom [] ((gctr256_lemma s) code_gctr256 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_gctr256 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gctr256_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    code_gctr256
    dom
    (W.mk_prediction code_gctr256 dom [] ((gctr256_lemma s) code_gctr256 IA.win))

[@ (CCConv "stdcall") ]
let gctr128_bytes //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr128_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr128_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr128 s)

[@ (CCConv "stdcall") ]
let gctr256_bytes //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr256_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr256_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gctr256 s)
