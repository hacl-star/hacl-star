module Fast_stdcalls

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module BV = LowStar.BufferView
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
let b64 = buf_t TUInt64
[@__reduce__] unfold
let t64_mod = TD_Buffer TUInt64 default_bq
[@__reduce__] unfold
let t64_no_mod = TD_Buffer TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] unfold
let tuint64 = TD_Base TUInt64

[@__reduce__]
let dom: IX64.arity_ok td =
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
      FU.va_req_fast_add1_stdcall c va_s0 IA.win (as_vale_buffer sb) 
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
      FU.va_ens_fast_add1_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

module VS = X64.Vale.State

#set-options "--z3rlimit 20"

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
       VSig.vale_calling_conventions va_s0 va_s1 /\
       add1_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_fast_add1_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let add1_lemma = as_t #(VSig.vale_sig add1_pre add1_post) add1_lemma'

let code_add1 = FU.va_code_fast_add1_stdcall IA.win

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_add1_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_add1
    16
    dom
    []
    _
    _
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

(* And here's the add1 wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  IX64.wrap
    Interop.down_mem
    code_add1
    16
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

let lowstar_add1_normal_t : normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

open Vale.AsLowStar.MemoryHelpers

let fast_add1
  (out:b8)
  (f1:b8)
  (f2:uint64) 
  : Stack uint64
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    (B.disjoint out f1 \/ out == f1))
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in    
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let d = pow2_five d0 d1 d2 d3 (UInt64.v c) in
    d = a + UInt64.v f2
    )
    )
  = 
  let x, _ = lowstar_add1_normal_t out f1 f2 () in
  x
  
open Vale.Interop.Cast

let add1 out f1 f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    copy_down out out8;
    copy_down f1 f18;
    let x = fast_add1 out8 f18 f2 in
    imm_copy_up f1 f18;
    copy_up out out8;
    pop_frame();
    x
    

[@__reduce__]
let fadd_dom: IX64.arity_ok td =
  let y = [t64_mod; t64_no_mod; t64_no_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fadd_pre : VSig.vale_pre 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FH.va_req_fadd_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fadd_post : VSig.vale_post 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fadd_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fadd_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fadd_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fadd_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fadd_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that add1_lemma' has the required type *)
let fadd_lemma = as_t #(VSig.vale_sig fadd_pre fadd_post) fadd_lemma'

let code_fadd = FH.va_code_fadd_stdcall IA.win

(* Here's the type expected for the add1 wrapper *)
[@__reduce__]
let lowstar_fadd_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fadd
    16
    fadd_dom
    []
    _
    _
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

(* And here's the fadd wrapper itself *)
let lowstar_fadd : lowstar_fadd_t  =
  IX64.wrap
    Interop.down_mem
    code_fadd
    16
    fadd_dom
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

let lowstar_fadd_normal_t //: normal lowstar_add1_t
  = as_normal_t #lowstar_fadd_t lowstar_fadd

let fast_fadd
  (out:b8)
  (f1:b8)
  (f2:b8) 
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f2 /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length f2 == 32 /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out f2 \/ out == f2) /\
    (B.disjoint f1 f2 \/ f1 == f2))
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 f2 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let b0 = UInt64.v (low_buffer_read TUInt64 h0 f2 0) in
    let b1 = UInt64.v (low_buffer_read TUInt64 h0 f2 1) in
    let b2 = UInt64.v (low_buffer_read TUInt64 h0 f2 2) in
    let b3 = UInt64.v (low_buffer_read TUInt64 h0 f2 3) in     
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let b = pow2_four b0 b1 b2 b3 in
    let d = pow2_four d0 d1 d2 d3 in
    d % prime = (a + b) % prime
    )
    )
  = 
  let x, _ = lowstar_fadd_normal_t out f1 f2 () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fadd out f1 f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f28 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    copy_down out out8;
    copy_down f2 f28;
    copy_down f1 f18;
    let x = fast_fadd out8 f18 f28 in
    imm_copy_up f1 f18;
    imm_copy_up f2 f28;
    copy_up out out8;
    pop_frame();
    x

#pop-options

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsub_pre : VSig.vale_pre 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FH.va_req_fsub_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2)

[@__reduce__]
let fsub_post : VSig.vale_post 16 fadd_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fsub_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) va_s1 f

[@__reduce__] unfold
let fsub_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsub_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fsub_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fsub_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f2;   
   va_s1, f                                   

(* Prove that fsub_lemma' has the required type *)
let fsub_lemma = as_t #(VSig.vale_sig fsub_pre fsub_post) fsub_lemma'

let code_fsub = FH.va_code_fsub_stdcall IA.win

(* Here's the type expected for the fsub wrapper *)
[@__reduce__]
let lowstar_fsub_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fsub
    16
    fadd_dom
    []
    _
    _
    (W.mk_prediction code_fsub fadd_dom [] (fsub_lemma code_fsub IA.win))

(* And here's the fsub wrapper itself *)
let lowstar_fsub : lowstar_fsub_t  =
  IX64.wrap
    Interop.down_mem
    code_fsub
    16
    fadd_dom
    (W.mk_prediction code_fsub fadd_dom [] (fsub_lemma code_fsub IA.win))

let lowstar_fsub_normal_t //: normal lowstar_fsub_t
  = as_normal_t #lowstar_fsub_t lowstar_fsub

let fast_fsub
  (out:b8)
  (f1:b8)
  (f2:b8) 
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f2 /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length f2 == 32 /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out f2 \/ out == f2) /\
    (B.disjoint f1 f2 \/ f1 == f2))
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 f2 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let b0 = UInt64.v (low_buffer_read TUInt64 h0 f2 0) in
    let b1 = UInt64.v (low_buffer_read TUInt64 h0 f2 1) in
    let b2 = UInt64.v (low_buffer_read TUInt64 h0 f2 2) in
    let b3 = UInt64.v (low_buffer_read TUInt64 h0 f2 3) in     
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let b = pow2_four b0 b1 b2 b3 in
    let d = pow2_four d0 d1 d2 d3 in
    d % prime = (a - b) % prime
    )
    )
  = 
  let x, _ = lowstar_fsub_normal_t out f1 f2 () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsub out f1 f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f28 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    copy_down out out8;
    copy_down f2 f28;
    copy_down f1 f18;
    let x = fast_fsub out8 f18 f28 in
    imm_copy_up f1 f18;
    imm_copy_up f2 f28;
    copy_up out out8;
    pop_frame();
    x

#pop-options

[@__reduce__]
let fmul_dom: IX64.arity_ok td =
  let y = [t64_mod; t64_no_mod; t64_mod; t64_no_mod] in
  assert_norm (List.length y = 4);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul_pre : VSig.vale_pre 48 fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48) ->
      FW.va_req_fmul_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__]
let fmul_post : VSig.vale_post 48 fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fmul_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fmul_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul_pre code tmp f1 out f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fmul_post code tmp f1 out f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none))) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fmul_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f2;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 tmp;      
   va_s1, f                                   

(* Prove that fmul_lemma' has the required type *)
let fmul_lemma = as_t #(VSig.vale_sig fmul_pre fmul_post) fmul_lemma'

let code_fmul = FW.va_code_fmul_stdcall IA.win

(* Here's the type expected for the fmul wrapper *)
[@__reduce__]
let lowstar_fmul_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fmul
    48
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_fmul fmul_dom [] (fmul_lemma code_fmul IA.win))

(* And here's the fmul wrapper itself *)
let lowstar_fmul : lowstar_fmul_t  =
  IX64.wrap
    Interop.down_mem
    code_fmul
    48
    fmul_dom
    (W.mk_prediction code_fmul fmul_dom [] (fmul_lemma code_fmul IA.win))

let lowstar_fmul_normal_t //: normal lowstar_fmul_t
  = as_normal_t #lowstar_fmul_t lowstar_fmul


let fast_fmul
  (tmp:b8)
  (f1:b8)
  (out:b8) 
  (f2:b8)
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f2 /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.live h tmp /\
    B.length f2 == 32 /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    B.length tmp == 64 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out f2 \/ out == f2) /\
    (B.disjoint out tmp \/ out == tmp) /\
    (B.disjoint f1 f2 \/ f1 == f2) /\
    B.disjoint f1 tmp /\
    B.disjoint f2 tmp)
  (ensures fun h0 c h1 ->
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 f2 /\ B.live h1 tmp /\
    B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let b0 = UInt64.v (low_buffer_read TUInt64 h0 f2 0) in
    let b1 = UInt64.v (low_buffer_read TUInt64 h0 f2 1) in
    let b2 = UInt64.v (low_buffer_read TUInt64 h0 f2 2) in
    let b3 = UInt64.v (low_buffer_read TUInt64 h0 f2 3) in     
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let b = pow2_four b0 b1 b2 b3 in
    let d = pow2_four d0 d1 d2 d3 in
    d % prime = (a * b) % prime
    )
    )
  = 
  let x, _ = lowstar_fmul_normal_t tmp f1 out f2 () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fmul tmp f1 out f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f28 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let tmp8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    copy_down out out8;
    copy_down f2 f28;
    copy_down f1 f18;
    copy_down tmp tmp8;
    let x = fast_fmul tmp8 f18 out8 f28 in
    imm_copy_up f1 f18;
    imm_copy_up f2 f28;
    copy_up tmp tmp8;
    copy_up out out8;
    pop_frame();
    x

#pop-options


(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul2_pre : VSig.vale_pre 48 fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48) ->
      FW.va_req_fmul2_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__]
let fmul2_post : VSig.vale_post 48 fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fmul2_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fmul2_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 48)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul2_pre code tmp f1 out f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fmul2_post code tmp f1 out f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f2) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\       
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none))) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fmul2_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f2;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 tmp;      
   va_s1, f                                   

(* Prove that fmul2_lemma' has the required type *)
let fmul2_lemma = as_t #(VSig.vale_sig fmul2_pre fmul2_post) fmul2_lemma'

let code_fmul2 = FW.va_code_fmul2_stdcall IA.win

(* Here's the type expected for the fmul wrapper *)
[@__reduce__]
let lowstar_fmul2_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fmul2
    48
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_fmul2 fmul_dom [] (fmul2_lemma code_fmul2 IA.win))

(* And here's the fmul2 wrapper itself *)
let lowstar_fmul2 : lowstar_fmul2_t  =
  IX64.wrap
    Interop.down_mem
    code_fmul2
    48
    fmul_dom
    (W.mk_prediction code_fmul2 fmul_dom [] (fmul2_lemma code_fmul2 IA.win))

let lowstar_fmul2_normal_t //: normal lowstar_fmul2_t
  = as_normal_t #lowstar_fmul2_t lowstar_fmul2

let fast_fmul2
  (tmp:b8)
  (f1:b8)
  (out:b8) 
  (f2:b8)
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f2 /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.live h tmp /\
    B.length f2 == 64 /\ 
    B.length out == 64 /\ 
    B.length f1 == 64 /\
    B.length tmp == 128 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out f2 \/ out == f2) /\
    (B.disjoint out tmp \/ out == tmp) /\
    (B.disjoint f1 f2 \/ f1 == f2) /\
    B.disjoint f1 tmp /\
    B.disjoint f2 tmp)
  (ensures fun h0 c h1 ->
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 f2 /\ B.live h1 tmp /\
    B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let b0 = UInt64.v (low_buffer_read TUInt64 h0 f2 0) in
    let b1 = UInt64.v (low_buffer_read TUInt64 h0 f2 1) in
    let b2 = UInt64.v (low_buffer_read TUInt64 h0 f2 2) in
    let b3 = UInt64.v (low_buffer_read TUInt64 h0 f2 3) in     
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let b = pow2_four b0 b1 b2 b3 in
    let d = pow2_four d0 d1 d2 d3 in
    let a0' = UInt64.v (low_buffer_read TUInt64 h0 f1 4) in
    let a1' = UInt64.v (low_buffer_read TUInt64 h0 f1 5) in
    let a2' = UInt64.v (low_buffer_read TUInt64 h0 f1 6) in
    let a3' = UInt64.v (low_buffer_read TUInt64 h0 f1 7) in
    let b0' = UInt64.v (low_buffer_read TUInt64 h0 f2 4) in
    let b1' = UInt64.v (low_buffer_read TUInt64 h0 f2 5) in
    let b2' = UInt64.v (low_buffer_read TUInt64 h0 f2 6) in
    let b3' = UInt64.v (low_buffer_read TUInt64 h0 f2 7) in     
    let d0' = UInt64.v (low_buffer_read TUInt64 h1 out 4) in
    let d1' = UInt64.v (low_buffer_read TUInt64 h1 out 5) in
    let d2' = UInt64.v (low_buffer_read TUInt64 h1 out 6) in
    let d3' = UInt64.v (low_buffer_read TUInt64 h1 out 7) in
    let a' = pow2_four a0' a1' a2' a3' in
    let b' = pow2_four b0' b1' b2' b3' in
    let d' = pow2_four d0' d1' d2' d3' in    
    d % prime = (a * b) % prime /\
    d' % prime = (a' * b') % prime    
    )
    )
  = 
  let x, _ = lowstar_fmul2_normal_t tmp f1 out f2 () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fmul2 tmp f1 out f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let f28 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let tmp8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 128) in
    copy_down out out8;
    copy_down f2 f28;
    copy_down f1 f18;
    copy_down tmp tmp8;
    let x = fast_fmul2 tmp8 f18 out8 f28 in
    imm_copy_up f1 f18;
    imm_copy_up f2 f28;
    copy_up tmp tmp8;
    copy_up out out8;
    pop_frame();
    x

#pop-options

[@__reduce__]
let fmul1_dom: IX64.arity_ok td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul1_pre : VSig.vale_pre 32 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 32) ->
      FH.va_req_fmul1_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let fmul1_post : VSig.vale_post 32 dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 32)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fmul1_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] unfold
let fmul1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 32)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul1_pre code out f1 f2 va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fmul1_post code out f1 f2 va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FH.va_lemma_fmul1_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   va_s1, f                                   

(* Prove that fmul1_lemma' has the required type *)
let fmul1_lemma = as_t #(VSig.vale_sig fmul1_pre fmul1_post) fmul1_lemma'

let code_fmul1 = FH.va_code_fmul1_stdcall IA.win

(* Here's the type expected for the fmul1 wrapper *)
[@__reduce__]
let lowstar_fmul1_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fmul1
    32
    fmul1_dom
    []
    _
    _
    (W.mk_prediction code_fmul1 dom [] (fmul1_lemma code_fmul1 IA.win))

(* And here's the fmul1 wrapper itself *)
let lowstar_fmul1 : lowstar_fmul1_t  =
  IX64.wrap
    Interop.down_mem
    code_fmul1
    32
    fmul1_dom
    (W.mk_prediction code_fmul1 fmul1_dom [] (fmul1_lemma code_fmul1 IA.win))

let lowstar_fmul1_normal_t : normal lowstar_fmul1_t
  = as_normal_t #lowstar_fmul1_t lowstar_fmul1

let fast_fmul1
  (out:b8)
  (f1:b8)
  (f2:uint64{UInt64.v f2 < 121665}) 
  : Stack uint64
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    (B.disjoint out f1 \/ out == f1))
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in    
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let d = pow2_four d0 d1 d2 d3 in
    d % prime = (a * UInt64.v f2) % prime
    )
    )
  = 
  let x, _ = lowstar_fmul1_normal_t out f1 f2 () in
  x

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fmul1 out f1 f2
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    copy_down out out8;
    copy_down f1 f18;
    let x = fast_fmul1 out8 f18 f2 in
    imm_copy_up f1 f18;
    copy_up out out8;
    pop_frame();
    ()
   
#pop-options

[@__reduce__]
let fsqr_dom: IX64.arity_ok td =
  let y = [t64_mod; t64_no_mod; t64_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr_pre : VSig.vale_pre 56 fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56) ->
      FW.va_req_fsqr_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr_post : VSig.vale_post 56 fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fsqr_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr_pre code tmp f1 out va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fsqr_post code tmp f1 out va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none))) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fsqr_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 tmp;   
   va_s1, f                                   

(* Prove that fsqr_lemma' has the required type *)
let fsqr_lemma = as_t #(VSig.vale_sig fsqr_pre fsqr_post) fsqr_lemma'

let code_fsqr = FW.va_code_fsqr_stdcall IA.win

(* Here's the type expected for the fsqr wrapper *)
[@__reduce__]
let lowstar_fsqr_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fsqr
    56
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

(* And here's the fsqr wrapper itself *)
let lowstar_fsqr : lowstar_fsqr_t  =
  IX64.wrap
    Interop.down_mem
    code_fsqr
    56
    fsqr_dom
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

let lowstar_fsqr_normal_t //: normal lowstar_fsqr_t
  = as_normal_t #lowstar_fsqr_t lowstar_fsqr

let fast_fsqr
  (tmp:b8)
  (f1:b8)
  (out:b8) 
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h tmp /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length tmp == 64 /\ 
    B.length out == 32 /\ 
    B.length f1 == 32 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out tmp \/ out == tmp) /\
    B.disjoint f1 tmp)
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 tmp /\
    B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let d = pow2_four d0 d1 d2 d3 in
    d % prime = (a * a) % prime
    )
    )
  = 
  let x, _ = lowstar_fsqr_normal_t tmp f1 out () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsqr tmp f1 out
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
    let tmp8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    copy_down out out8;
    copy_down tmp tmp8;
    copy_down f1 f18;
    let x = fast_fsqr tmp8 f18 out8 in
    imm_copy_up f1 f18;
    copy_up tmp tmp8;
    copy_up out out8;
    pop_frame();
    x

#pop-options

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr2_pre : VSig.vale_pre 56 fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56) ->
      FW.va_req_fsqr2_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr2_post : VSig.vale_post 56 fsqr_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fsqr2_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 100"

[@__reduce__] unfold
let fsqr2_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 56)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr2_pre code tmp f1 out va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       fsqr2_post code tmp f1 out va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer f1) /\ 
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer tmp) /\ 
       ME.buffer_writeable (as_vale_buffer out) /\ 
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\       
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none))) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FW.va_lemma_fsqr2_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 out;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 f1;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 tmp;   
   va_s1, f                                   

(* Prove that fsqr2_lemma' has the required type *)
let fsqr2_lemma = as_t #(VSig.vale_sig fsqr2_pre fsqr2_post) fsqr2_lemma'

let code_fsqr2 = FW.va_code_fsqr2_stdcall IA.win

(* Here's the type expected for the fsqr2 wrapper *)
[@__reduce__]
let lowstar_fsqr2_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_fsqr2
    56
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

(* And here's the fsqr2 wrapper itself *)
let lowstar_fsqr2 : lowstar_fsqr2_t  =
  IX64.wrap
    Interop.down_mem
    code_fsqr2
    56
    fsqr_dom
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

let lowstar_fsqr2_normal_t //: normal lowstar_fsqr2_t
  = as_normal_t #lowstar_fsqr2_t lowstar_fsqr2

let fast_fsqr2
  (tmp:b8)
  (f1:b8)
  (out:b8) 
  : Stack unit
  (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h tmp /\
    B.live h f1 /\ 
    B.live h out /\ 
    B.length tmp == 128 /\ 
    B.length out == 64 /\ 
    B.length f1 == 64 /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out tmp \/ out == tmp) /\
    B.disjoint f1 tmp)
  (ensures fun h0 c h1 -> 
    B.live h1 out /\ B.live h1 f1 /\ B.live h1 tmp /\
    B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
    (
    let a0 = UInt64.v (low_buffer_read TUInt64 h0 f1 0) in
    let a1 = UInt64.v (low_buffer_read TUInt64 h0 f1 1) in
    let a2 = UInt64.v (low_buffer_read TUInt64 h0 f1 2) in
    let a3 = UInt64.v (low_buffer_read TUInt64 h0 f1 3) in
    let d0 = UInt64.v (low_buffer_read TUInt64 h1 out 0) in
    let d1 = UInt64.v (low_buffer_read TUInt64 h1 out 1) in
    let d2 = UInt64.v (low_buffer_read TUInt64 h1 out 2) in
    let d3 = UInt64.v (low_buffer_read TUInt64 h1 out 3) in
    let a = pow2_four a0 a1 a2 a3 in
    let d = pow2_four d0 d1 d2 d3 in
    let a0' = UInt64.v (low_buffer_read TUInt64 h0 f1 4) in
    let a1' = UInt64.v (low_buffer_read TUInt64 h0 f1 5) in
    let a2' = UInt64.v (low_buffer_read TUInt64 h0 f1 6) in
    let a3' = UInt64.v (low_buffer_read TUInt64 h0 f1 7) in
    let d0' = UInt64.v (low_buffer_read TUInt64 h1 out 4) in
    let d1' = UInt64.v (low_buffer_read TUInt64 h1 out 5) in
    let d2' = UInt64.v (low_buffer_read TUInt64 h1 out 6) in
    let d3' = UInt64.v (low_buffer_read TUInt64 h1 out 7) in
    let a' = pow2_four a0' a1' a2' a3' in
    let d' = pow2_four d0' d1' d2' d3' in    
    d % prime = (a * a) % prime /\
    d' % prime = (a' * a') % prime   
    )
    )
  = 
  let x, _ = lowstar_fsqr2_normal_t tmp f1 out () in
  ()


#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let fsqr2 tmp f1 out
  = push_frame();
    let out8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let f18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let tmp8 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 128) in
    copy_down out out8;
    copy_down tmp tmp8;
    copy_down f1 f18;
    let x = fast_fsqr2 tmp8 f18 out8 in
    imm_copy_up f1 f18;
    copy_up tmp tmp8;
    copy_up out out8;
    pop_frame();
    x

#pop-options

[@__reduce__]
let cswap_dom: IX64.arity_ok td =
  let y = [t64_mod; t64_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let cswap_pre : VSig.vale_pre 16 cswap_dom =
  fun (c:V.va_code)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16) ->
      FU.va_req_cswap2_stdcall c va_s0 IA.win (as_vale_buffer sb) 
        (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit)

[@__reduce__]
let cswap_post : VSig.vale_post 16 cswap_dom =
  fun (c:V.va_code)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_cswap2_stdcall c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] unfold
let cswap_lemma'
    (code:V.va_code)
    (_win:bool)
    (p0:b64)
    (p1:b64)
    (bit:uint64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer 16)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       cswap_pre code p0 p1 bit va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       cswap_post code p0 p1 bit va_s0 sb va_s1 f /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer p1) /\
       ME.buffer_readable VS.(va_s1.mem) (as_vale_buffer p0) /\ 
       ME.buffer_writeable (as_vale_buffer p0) /\ 
       ME.buffer_writeable (as_vale_buffer p1) /\ 
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer sb))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer p0))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer p1))
                                 ME.loc_none))) va_s0.VS.mem va_s1.VS.mem
 )) = 
   let va_s1, f = FU.va_lemma_cswap2_stdcall code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer p0) (as_vale_buffer p1) (UInt64.v bit) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 p0;   
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 p1;   
   va_s1, f                                   

(* Prove that cswap_lemma' has the required type *)
let cswap_lemma = as_t #(VSig.vale_sig cswap_pre cswap_post) cswap_lemma'

let code_cswap = FU.va_code_cswap2_stdcall IA.win

(* Here's the type expected for the cswap wrapper *)
[@__reduce__]
let lowstar_cswap_t =
  IX64.as_lowstar_sig_t_weak
    Interop.down_mem
    code_cswap
    16
    cswap_dom
    []
    _
    _
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

(* And here's the cswap wrapper itself *)
let lowstar_cswap : lowstar_cswap_t  =
  IX64.wrap
    Interop.down_mem
    code_cswap
    16
    cswap_dom
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

let lowstar_cswap_normal_t : normal lowstar_cswap_t
  = as_normal_t #lowstar_cswap_t lowstar_cswap

#set-options "--z3rlimit 100"

let fast_cswap2
  (p0:b8)
  (p1:b8)
  (bit:uint64) 
  : Stack unit
  (requires fun h -> 
    UInt64.v bit <= 1 /\
    B.live h p0 /\ 
    B.live h p1 /\ 
    B.length p0 == 64 /\ 
    B.length p1 == 64 /\
    (B.disjoint p0 p1 \/ p0 == p1))
  (ensures fun h0 _ h1 -> 
    B.live h1 p0 /\ B.live h1 p1 /\
    B.modifies (B.loc_union (B.loc_buffer p0) (B.loc_buffer p1)) h0 h1 /\
    (
      (UInt64.v bit = 1 ==>
        low_buffer_read TUInt64 h0 p0 0 == low_buffer_read TUInt64 h1 p1 0 /\
        low_buffer_read TUInt64 h0 p0 1 == low_buffer_read TUInt64 h1 p1 1 /\
        low_buffer_read TUInt64 h0 p0 2 == low_buffer_read TUInt64 h1 p1 2 /\
        low_buffer_read TUInt64 h0 p0 3 == low_buffer_read TUInt64 h1 p1 3 /\
        low_buffer_read TUInt64 h0 p0 4 == low_buffer_read TUInt64 h1 p1 4 /\
        low_buffer_read TUInt64 h0 p0 5 == low_buffer_read TUInt64 h1 p1 5 /\
        low_buffer_read TUInt64 h0 p0 6 == low_buffer_read TUInt64 h1 p1 6 /\
        low_buffer_read TUInt64 h0 p0 7 == low_buffer_read TUInt64 h1 p1 7 /\        
        
        low_buffer_read TUInt64 h0 p1 0 == low_buffer_read TUInt64 h1 p0 0 /\
        low_buffer_read TUInt64 h0 p1 1 == low_buffer_read TUInt64 h1 p0 1 /\
        low_buffer_read TUInt64 h0 p1 2 == low_buffer_read TUInt64 h1 p0 2 /\
        low_buffer_read TUInt64 h0 p1 3 == low_buffer_read TUInt64 h1 p0 3 /\
        low_buffer_read TUInt64 h0 p1 4 == low_buffer_read TUInt64 h1 p0 4 /\
        low_buffer_read TUInt64 h0 p1 5 == low_buffer_read TUInt64 h1 p0 5 /\
        low_buffer_read TUInt64 h0 p1 6 == low_buffer_read TUInt64 h1 p0 6 /\
        low_buffer_read TUInt64 h0 p1 7 == low_buffer_read TUInt64 h1 p0 7
      ) /\
      (UInt64.v bit = 0 ==>
        low_buffer_read TUInt64 h0 p0 0 == low_buffer_read TUInt64 h1 p0 0 /\
        low_buffer_read TUInt64 h0 p0 1 == low_buffer_read TUInt64 h1 p0 1 /\
        low_buffer_read TUInt64 h0 p0 2 == low_buffer_read TUInt64 h1 p0 2 /\
        low_buffer_read TUInt64 h0 p0 3 == low_buffer_read TUInt64 h1 p0 3 /\
        low_buffer_read TUInt64 h0 p0 4 == low_buffer_read TUInt64 h1 p0 4 /\
        low_buffer_read TUInt64 h0 p0 5 == low_buffer_read TUInt64 h1 p0 5 /\
        low_buffer_read TUInt64 h0 p0 6 == low_buffer_read TUInt64 h1 p0 6 /\
        low_buffer_read TUInt64 h0 p0 7 == low_buffer_read TUInt64 h1 p0 7 /\        
        
        low_buffer_read TUInt64 h0 p1 0 == low_buffer_read TUInt64 h1 p1 0 /\
        low_buffer_read TUInt64 h0 p1 1 == low_buffer_read TUInt64 h1 p1 1 /\
        low_buffer_read TUInt64 h0 p1 2 == low_buffer_read TUInt64 h1 p1 2 /\
        low_buffer_read TUInt64 h0 p1 3 == low_buffer_read TUInt64 h1 p1 3 /\
        low_buffer_read TUInt64 h0 p1 4 == low_buffer_read TUInt64 h1 p1 4 /\
        low_buffer_read TUInt64 h0 p1 5 == low_buffer_read TUInt64 h1 p1 5 /\
        low_buffer_read TUInt64 h0 p1 6 == low_buffer_read TUInt64 h1 p1 6 /\
        low_buffer_read TUInt64 h0 p1 7 == low_buffer_read TUInt64 h1 p1 7
      )
    ))
  = 
  let x, _ = lowstar_cswap_normal_t p0 p1 bit () in
  ()

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let cswap2 p0 p1 bit
  = push_frame();
    let p08 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    let p18 = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 64) in
    copy_down p0 p08;
    copy_down p1 p18;
    let x = fast_cswap2 p08 p18 bit in
    copy_up p1 p18;
    copy_up p0 p08;
    pop_frame();
    x
    
#pop-options
