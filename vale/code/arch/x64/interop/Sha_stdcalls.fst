module Sha_stdcalls

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

module SH = X64.SHA

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] unfold
let b128 = buf_t TUInt32 TUInt128
[@__reduce__] unfold
let b8_128 = buf_t TUInt8 TUInt128
[@__reduce__] unfold
let ib128 = ibuf_t TUInt32 TUInt128
[@__reduce__] unfold
let t128_mod = TD_Buffer TUInt32 TUInt128 default_bq
[@__reduce__] unfold
let t128_no_mod = TD_Buffer TUInt8 TUInt128 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] unfold
let t128_imm = TD_ImmBuffer TUInt32 TUInt128 default_bq
[@__reduce__] unfold
let tuint64 = TD_Base TUInt64

[@__reduce__]
let dom: IX64.arity_ok_stdcall td =
  let y = [t128_mod; t128_no_mod; tuint64; t128_imm] in
  assert_norm (List.length y = 4);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let sha_pre : VSig.vale_pre 224 dom =
  fun (c:V.va_code)
    (ctx_b:b128)
    (in_b:b8_128)
    (num_val:uint64)
    (k_b:ib128)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 224) ->
      SH.va_req_sha_update_bytes_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer ctx_b) (as_vale_buffer in_b) (UInt64.v num_val) (as_vale_immbuffer k_b)

(* Need to rearrange the order of arguments *)
[@__reduce__]
let sha_post : VSig.vale_post 224 dom =
  fun (c:V.va_code)
    (ctx_b:b128)
    (in_b:b8_128)
    (num_val:uint64)
    (k_b:ib128)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 224)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      SH.va_ens_sha_update_bytes_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer ctx_b) (as_vale_buffer in_b) (UInt64.v num_val) (as_vale_immbuffer k_b)
        va_s1 f


module VS = X64.Vale.State

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

[@__reduce__] unfold
let sha_lemma'
    (code:V.va_code)
    (_win:bool)
    (ctx_b:b128)
    (in_b:b8_128)
    (num_val:uint64)
    (k_b:ib128)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 224)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       sha_pre code ctx_b in_b num_val k_b va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       sha_post code ctx_b in_b num_val k_b va_s0 sb va_s1 f /\       
       ME.buffer_writeable (as_vale_buffer ctx_b) /\ 
       ME.buffer_writeable (as_vale_buffer in_b)
 )) = 
   let va_s1, f = SH.va_lemma_sha_update_bytes_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer ctx_b) (as_vale_buffer in_b) (UInt64.v num_val) (as_vale_immbuffer k_b) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt32 ME.TUInt128 ctx_b;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt128 in_b;  
   va_s1, f                                   

(* Prove that sha_lemma' has the required type *)
let sha_lemma = as_t #(VSig.vale_sig_stdcall sha_pre sha_post) sha_lemma'

let code_sha = SH.va_code_sha_update_bytes_stdcall IA.win

#reset-options "--z3rlimit 20"

(* Here's the type expected for the sha wrapper *)
[@__reduce__]
let lowstar_sha_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    Interop.down_mem
    code_sha
    224
    dom
    []
    _
    _
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

(* And here's the sha wrapper itself *)
let lowstar_sha : lowstar_sha_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_sha
    224
    dom
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

let lowstar_sha_normal_t : normal lowstar_sha_t
  = as_normal_t #lowstar_sha_t lowstar_sha

open Vale.AsLowStar.MemoryHelpers
open Words.Seq_s

open Simplify_Sha

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma ( ((64 * n) * 1) / 16 == 4 * n) = ()

let sha256_update ctx_b in_b num_val k_b =
  let h0 = get() in
  DV.length_eq (get_downview in_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in_b);
  DV.length_eq (get_downview ctx_b);
  DV.length_eq (get_downview k_b);
  lemma_k_reqs_equiv k_b h0; 
  math_aux (UInt64.v num_val);
  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  let x, _ = lowstar_sha_normal_t ctx_b in_b num_val k_b () in
  let h1 = get() in
  reveal_word();
  simplify_le_bytes_to_hash_uint32 ctx_b h0;
  simplify_le_bytes_to_hash_uint32 ctx_b h1;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h0;
  ()
