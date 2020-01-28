module Vale.Stdcalls.X64.Fswap
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
let cswap_dom: IX64.arity_ok_stdcall td =
  let y = [tuint64; t64_mod; t64_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__] noextract
let cswap_pre : VSig.vale_pre cswap_dom =
  fun (c:V.va_code)
    (bit:uint64)
    (p0:b64)
    (p1:b64)
    (va_s0:V.va_state) ->
      FU.va_req_Cswap2_stdcall c va_s0 IA.win
        (UInt64.v bit) (as_vale_buffer p0) (as_vale_buffer p1)

[@__reduce__] noextract
let cswap_post : VSig.vale_post cswap_dom =
  fun (c:V.va_code)
    (bit:uint64)
    (p0:b64)
    (p1:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FU.va_ens_Cswap2_stdcall c va_s0 IA.win (UInt64.v bit) (as_vale_buffer p0) (as_vale_buffer p1) va_s1 f

#set-options "--z3rlimit 20"

[@__reduce__] noextract
let cswap_lemma'
    (code:V.va_code)
    (_win:bool)
    (bit:uint64)
    (p0:b64)
    (p1:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       cswap_pre code bit p0 p1 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       cswap_post code bit p0 p1 va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer p1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer p0) /\
       ME.buffer_writeable (as_vale_buffer p0) /\
       ME.buffer_writeable (as_vale_buffer p1) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer p0))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer p1))
                                 ME.loc_none)) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FU.va_lemma_Cswap2_stdcall code va_s0 IA.win (UInt64.v bit) (as_vale_buffer p0) (as_vale_buffer p1) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 p0;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 p1;
   (va_s1, f)

(* Prove that cswap_lemma' has the required type *)
noextract
let cswap_lemma = as_t #(VSig.vale_sig_stdcall cswap_pre cswap_post) cswap_lemma'
noextract
let code_cswap = FU.va_code_Cswap2_stdcall IA.win

(* Here's the type expected for the cswap wrapper *)
[@__reduce__] noextract
let lowstar_cswap_t =
  assert_norm (List.length cswap_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak_stdcall
    code_cswap
    cswap_dom
    []
    _
    _
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

[@ (CCConv "stdcall") ]
val cswap2_e : normal lowstar_cswap_t
