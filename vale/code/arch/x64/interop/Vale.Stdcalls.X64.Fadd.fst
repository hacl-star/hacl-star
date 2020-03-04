module Vale.Stdcalls.X64.Fadd
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
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

module FU = Vale.Curve25519.X64.FastUtil
module FH = Vale.Curve25519.X64.FastHybrid
module FW = Vale.Curve25519.X64.FastWide

(* And here's the fadd wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_add1
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

let add_scalar_e //: normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

(* And here's the fadd wrapper itself *)
let lowstar_fadd : lowstar_fadd_t  =
  assert_norm (List.length fadd_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fadd
    fadd_dom
    (W.mk_prediction code_Fadd fadd_dom [] (fadd_lemma code_Fadd IA.win))

let fadd_e //: normal lowstar_add1_t
= as_normal_t #lowstar_fadd_t lowstar_fadd
