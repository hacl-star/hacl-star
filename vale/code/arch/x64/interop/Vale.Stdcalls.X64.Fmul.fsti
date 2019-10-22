module Vale.Stdcalls.X64.Fmul
open FStar.Mul

val z3rlimit_hack (x:nat) : squash (x < x + x + 1)
#reset-options "--z3rlimit 50"

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
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
open Vale.AsLowStar.MemoryHelpers

module FU = Vale.Curve25519.X64.FastUtil
module FH = Vale.Curve25519.X64.FastHybrid
module FW = Vale.Curve25519.X64.FastWide

let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
noextract
let as_t (#a:Type) (x:normal a) : a = x
noextract
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__] noextract
let b64 = buf_t TUInt64 TUInt64
[@__reduce__] noextract
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__] noextract
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__] noextract
let tuint64 = TD_Base TUInt64

[@__reduce__] noextract
let fmul_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; t64_mod; t64_no_mod] in
  assert_norm (List.length y = 4);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let fmul_pre : VSig.vale_pre fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fmul_stdcall c va_s0 IA.win
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__] noextract
let fmul_post : VSig.vale_post fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fmul_stdcall c va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__] noextract
let fmul_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul_pre code tmp f1 out f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       fmul_post code tmp f1 out f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer f2) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) va_s0.VS.vs_heap va_s1.VS.vs_heap
 )) =
   let va_s1, f = FW.va_lemma_fmul_stdcall code va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fmul_lemma' has the required type *)
noextract
let fmul_lemma = as_t #(VSig.vale_sig_stdcall fmul_pre fmul_post) fmul_lemma'
noextract
let code_fmul = FW.va_code_fmul_stdcall IA.win

(* Here's the type expected for the fmul wrapper *)
[@__reduce__] noextract
let lowstar_fmul_t =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_fmul
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_fmul fmul_dom [] (fmul_lemma code_fmul IA.win))

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let fmul2_pre : VSig.vale_pre fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state) ->
      FW.va_req_fmul2_stdcall c va_s0 IA.win
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__] noextract
let fmul2_post : VSig.vale_post fmul_dom =
  fun (c:V.va_code)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_fmul2_stdcall c va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__] noextract
let fmul2_lemma'
    (code:V.va_code)
    (_win:bool)
    (tmp:b64)
    (f1:b64)
    (out:b64)
    (f2:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul2_pre code tmp f1 out f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       fmul2_post code tmp f1 out f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer out) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer f2) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) va_s0.VS.vs_heap va_s1.VS.vs_heap
 )) =
   let va_s1, f = FW.va_lemma_fmul2_stdcall code va_s0 IA.win (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fmul2_lemma' has the required type *)
noextract
let fmul2_lemma = as_t #(VSig.vale_sig_stdcall fmul2_pre fmul2_post) fmul2_lemma'
noextract
let code_fmul2 = FW.va_code_fmul2_stdcall IA.win

(* Here's the type expected for the fmul wrapper *)
[@__reduce__] noextract
let lowstar_fmul2_t =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_fmul2
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_fmul2 fmul_dom [] (fmul2_lemma code_fmul2 IA.win))

[@__reduce__] noextract
let fmul1_dom: IX64.arity_ok_stdcall td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let fmul1_pre : VSig.vale_pre fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state) ->
      FH.va_req_fmul1_stdcall c va_s0 IA.win
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__] noextract
let fmul1_post : VSig.vale_post fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_fmul1_stdcall c va_s0 IA.win (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 50"

[@__reduce__] noextract
let fmul1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul1_pre code out f1 f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       fmul1_post code out f1 f2 va_s0 va_s1 f /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer f1) /\
       ME.buffer_readable VS.(va_s1.vs_heap) (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none) va_s0.VS.vs_heap va_s1.VS.vs_heap
 )) =
   let va_s1, f = FH.va_lemma_fmul1_stdcall code va_s0 IA.win (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
let s0 = va_s0 in
let s1 = va_s1 in
let regs_modified = IX64.regs_modified_stdcall in
let xmms_modified = IX64.xmms_modified_stdcall in
let open MS in
let open Vale.AsLowStar.ValeSig in
assert (forall (r:MS.reg_64).{:pattern vale_save_reg r s0 s1} not (regs_modified r) ==> vale_save_reg r s0 s1);
assert (forall (x:MS.reg_xmm).{:pattern vale_save_xmm x s0 s1} not (xmms_modified x) ==> vale_save_xmm x s0 s1);
   (va_s1, f)

(* Prove that fmul1_lemma' has the required type *)
noextract
let fmul1_lemma = as_t #(VSig.vale_sig_stdcall fmul1_pre fmul1_post) fmul1_lemma'
noextract
let code_fmul1 = FH.va_code_fmul1_stdcall IA.win

(* Here's the type expected for the fmul1 wrapper *)
[@__reduce__] noextract
let lowstar_fmul1_t =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_fmul1
    fmul1_dom
    []
    _
    _
    (W.mk_prediction code_fmul1 fmul1_dom [] (fmul1_lemma code_fmul1 IA.win))

[@ (CCConv "stdcall") ]
val fmul_ : normal lowstar_fmul_t

[@ (CCConv "stdcall") ]
val fmul2 : normal lowstar_fmul2_t

[@ (CCConv "stdcall") ]
val fmul1 : normal lowstar_fmul1_t
