module Fadd_inline

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
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

module FU = X64.FastUtil
module FH = X64.FastHybrid
module FW = X64.FastWide

let b8 = B.buffer UInt8.t
let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] unfold
let b64 = buf_t TUInt64 TUInt64
[@__reduce__] unfold
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__] unfold
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] unfold
let tuint64 = TD_Base TUInt64

// static inline uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b) {
//   register uint64_t* dst_r asm("rdi") = dst;
//   register uint64_t* in_a_r asm("rsi") = in_a;
//   register uint64_t* b_r asm("rdx") = b;
//   register uint64_t* carry_r asm("rax");

//   __asm__ __volatile__(
//     "  xor %%r8, %%r8;"
//     "  xor %%r9, %%r9;"
//     "  xor %%r10, %%r10;"
//     "  xor %%r11, %%r11;"
//     "  xor %%rax, %%rax;"
//     "  addq 0(%%rsi), %%rcx;"
//     "  movq %%rcx, 0(%%rdi);"
//     "  adcxq 8(%%rsi), %%r8;"
//     "  movq %%r8, 8(%%rdi);"
//     "  adcxq 16(%%rsi), %%r9;"
//     "  movq %%r9, 16(%%rdi);"
//     "  adcxq 24(%%rsi), %%r10;"
//     "  movq %%r10, 24(%%rdi);"
//     "  adcx %%r11, %%rax;"
//   : "=r" (carry_r), "+r" (b_r)
//   : "r" (dst_r), "r" (in_a_r)
//   : "memory", "cc", "%r8", "%r9", "%r10", "%r11"
//   );
// }

[@__reduce__] unfold
let dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let add1_pre : VSig.vale_pre 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FU.va_req_fast_add1 c va_s0 (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let add1_post : VSig.vale_post 16 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_fast_add1 c va_s0 (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 50"

let regs_modified: MS.reg -> bool = fun (r:MS.reg) ->
  let open MS in
  if r = Rax || r = Rdx || r = R8 || r = R9 || r = R10 || r = R11 then true
  else false

let xmms_modified = fun _ -> false

[@__reduce__] unfold
let add1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       add1_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 regs_modified xmms_modified /\
       add1_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_fast_add1 code va_s0 (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let add1_lemma = as_t #(VSig.vale_sig regs_modified xmms_modified add1_pre add1_post) add1_lemma'

let code_add1 = FU.va_code_fast_add1 ()

let of_reg (r:MS.reg) : option (IX64.reg_nat 3) = match r with
  | MS.Rdi -> Some 0
  | MS.Rsi -> Some 1
  | MS.Rdx -> Some 2
  | _ -> None

let of_arg (i:IX64.reg_nat 3) = match i with
  | 0 -> MS.Rdi
  | 1 -> MS.Rsi
  | 2 -> MS.Rdx

let arg_reg : IX64.arg_reg_relation 3 = IX64.Rel of_reg of_arg

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_add1_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    regs_modified
    xmms_modified
    Interop.down_mem
    code_add1
    16
    dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

(* And here's the add1 wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    regs_modified
    xmms_modified
    Interop.down_mem
    code_add1
    16
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

let lowstar_add1_normal_t : normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

open Vale.AsLowStar.MemoryHelpers

let add1_inline out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    let x, _ = lowstar_add1_normal_t out f1 f2 () in
    x
