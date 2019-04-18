module Vale.Stdcalls.GCMdecryptOpt

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open FStar.Mul

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

module GC = X64.GCMdecryptOpt
open AES_s

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
  let y = [t128_no_mod; tuint64; tuint64; t128_no_mod; t128_mod; t128_no_mod;
    t128_no_mod; t128_no_mod; t128_mod; tuint64; t128_no_mod; t128_mod; tuint64; t128_mod; tuint64; t128_mod; t128_no_mod] in
  assert_norm (List.length y = 17);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gcm128_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128)
    (va_s0:V.va_state) ->
      GC.va_req_gcm_blocks_decrypt_stdcall c va_s0 IA.win AES_128
        (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b)
        (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b) (Ghost.reveal s)

[@__reduce__] noextract
let gcm128_post : Ghost.erased (Seq.seq nat32) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128) 
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GC.va_ens_gcm_blocks_decrypt_stdcall c va_s0 IA.win AES_128
       (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b) (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b)
      (Ghost.reveal s) va_s1 f

#set-options "--z3rlimit 50"

[@__reduce__] noextract
let gcm128_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128)     
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       gcm128_pre s code auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
         in128x6_b out128x6_b len128x6_num in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       gcm128_post s code auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
         in128x6_b out128x6_b len128x6_num in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer auth_b) /\ 
       ME.buffer_writeable (as_vale_buffer keys_b) /\ 
       ME.buffer_writeable (as_vale_buffer iv_b) /\ 
       ME.buffer_writeable (as_vale_buffer hkeys_b) /\ 
       ME.buffer_writeable (as_vale_buffer abytes_b) /\ 
       ME.buffer_writeable (as_vale_buffer in128x6_b) /\
       ME.buffer_writeable (as_vale_buffer out128x6_b) /\ 
       ME.buffer_writeable (as_vale_buffer in128_b) /\ 
       ME.buffer_writeable (as_vale_buffer out128_b) /\ 
       ME.buffer_writeable (as_vale_buffer inout_b) /\
       ME.buffer_writeable (as_vale_buffer scratch_b) /\ 
       ME.buffer_writeable (as_vale_buffer tag_b)
 )) = 
    let va_s1, f = GC.va_lemma_gcm_blocks_decrypt_stdcall code va_s0 IA.win AES_128
       (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b)
        (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b)   
       (Ghost.reveal s) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 auth_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 keys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 iv_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 hkeys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 abytes_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in128x6_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out128x6_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in128_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out128_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 inout_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 scratch_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 tag_b;   
   va_s1, f

(* Prove that gcm128_lemma' has the required type *)
noextract
let gcm128_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (gcm128_pre s) (gcm128_post s)) (gcm128_lemma' s)

noextract
let code_gcm128 = GC.va_code_gcm_blocks_decrypt_stdcall IA.win AES_128

(* Here's the type expected for the gcm wrapper *)
[@__reduce__] noextract
let lowstar_gcm128_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_gcm128
    dom
    []
    _
    _
    (W.mk_prediction code_gcm128 dom [] ((gcm128_lemma s) code_gcm128 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_gcm128 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gcm128_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_gcm128
    dom
    (W.mk_prediction code_gcm128 dom [] ((gcm128_lemma s) code_gcm128 IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let gcm256_pre : (Ghost.erased (Seq.seq nat32)) -> VSig.vale_pre dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128)
    (va_s0:V.va_state) ->
      GC.va_req_gcm_blocks_decrypt_stdcall c va_s0 IA.win AES_256
        (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b)
        (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b) (Ghost.reveal s)

[@__reduce__] noextract
let gcm256_post : Ghost.erased (Seq.seq nat32) -> VSig.vale_post dom =
  fun (s:Ghost.erased (Seq.seq nat32))
    (c:V.va_code)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128) 
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      GC.va_ens_gcm_blocks_decrypt_stdcall c va_s0 IA.win AES_256
       (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b) (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b)
      (Ghost.reveal s) va_s1 f

#set-options "--z3rlimit 50"

[@__reduce__] noextract
let gcm256_lemma'
    (s:Ghost.erased (Seq.seq nat32))
    (code:V.va_code)
    (_win:bool)
    (auth_b:b128)
    (auth_bytes:uint64)
    (auth_num:uint64)
    (keys_b:b128)
    (iv_b:b128)
    (hkeys_b:b128)
    (abytes_b:b128)
    (in128x6_b:b128)
    (out128x6_b:b128)
    (len128x6_num:uint64)
    (in128_b:b128)
    (out128_b:b128)
    (len128_num:uint64)
    (inout_b:b128)
    (cipher_num:uint64)
    (scratch_b:b128)
    (tag_b:b128)     
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       gcm256_pre s code auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
         in128x6_b out128x6_b len128x6_num in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       gcm256_post s code auth_b auth_bytes auth_num keys_b iv_b hkeys_b abytes_b
         in128x6_b out128x6_b len128x6_num in128_b out128_b len128_num inout_b cipher_num scratch_b tag_b va_s0 va_s1 f /\
       ME.buffer_writeable (as_vale_buffer auth_b) /\ 
       ME.buffer_writeable (as_vale_buffer keys_b) /\ 
       ME.buffer_writeable (as_vale_buffer iv_b) /\ 
       ME.buffer_writeable (as_vale_buffer hkeys_b) /\ 
       ME.buffer_writeable (as_vale_buffer abytes_b) /\ 
       ME.buffer_writeable (as_vale_buffer in128x6_b) /\
       ME.buffer_writeable (as_vale_buffer out128x6_b) /\ 
       ME.buffer_writeable (as_vale_buffer in128_b) /\ 
       ME.buffer_writeable (as_vale_buffer out128_b) /\ 
       ME.buffer_writeable (as_vale_buffer inout_b) /\
       ME.buffer_writeable (as_vale_buffer scratch_b) /\ 
       ME.buffer_writeable (as_vale_buffer tag_b)
 )) = 
    let va_s1, f = GC.va_lemma_gcm_blocks_decrypt_stdcall code va_s0 IA.win AES_256
       (as_vale_buffer auth_b) (UInt64.v auth_bytes)
        (UInt64.v auth_num) (as_vale_buffer keys_b)
        (as_vale_buffer iv_b) (as_vale_buffer hkeys_b)
        (as_vale_buffer abytes_b) (as_vale_buffer in128x6_b)
        (as_vale_buffer out128x6_b) (UInt64.v len128x6_num)
        (as_vale_buffer in128_b)  (as_vale_buffer out128_b)
        (UInt64.v len128_num) (as_vale_buffer inout_b)
        (UInt64.v cipher_num)
        (as_vale_buffer scratch_b) (as_vale_buffer tag_b)   
       (Ghost.reveal s) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 auth_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 keys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 iv_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 hkeys_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 abytes_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in128x6_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out128x6_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in128_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 out128_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 inout_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 scratch_b;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 tag_b;   
   va_s1, f

(* Prove that gcm256_lemma' has the required type *)
noextract
let gcm256_lemma (s:Ghost.erased (Seq.seq nat32)) = as_t #(VSig.vale_sig_stdcall (gcm256_pre s) (gcm256_post s)) (gcm256_lemma' s)

noextract
let code_gcm256 = GC.va_code_gcm_blocks_decrypt_stdcall IA.win AES_256

(* Here's the type expected for the gcm wrapper *)
[@__reduce__] noextract
let lowstar_gcm256_t (s:Ghost.erased (Seq.seq nat32)) =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_gcm256
    dom
    []
    _
    _
    (W.mk_prediction code_gcm256 dom [] ((gcm256_lemma s) code_gcm256 IA.win))

(* And here's the gcm wrapper itself *)
noextract
let lowstar_gcm256 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gcm256_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_gcm256
    dom
    (W.mk_prediction code_gcm256 dom [] ((gcm256_lemma s) code_gcm256 IA.win))

[@ (CCConv "stdcall") ]
let gcm128_decrypt_opt //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128 s)

[@ (CCConv "stdcall") ]
let gcm256_decrypt_opt //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256_t s)
  = as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256 s)
