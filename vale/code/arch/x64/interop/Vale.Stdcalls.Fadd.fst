module Vale.Stdcalls.Fadd

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
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

module FU = X64.FastUtil
module FH = X64.FastHybrid
module FW = X64.FastWide

(* And here's the fadd wrapper itself *)
let lowstar_add1 : lowstar_add1_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_add1
    dom
    (W.mk_prediction code_add1 dom [] (add1_lemma code_add1 IA.win))

let add1 //: normal lowstar_add1_t
  = as_normal_t #lowstar_add1_t lowstar_add1

(* And here's the fadd wrapper itself *)
let lowstar_fadd : lowstar_fadd_t  =
  assert_norm (List.length fadd_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fadd
    fadd_dom
    (W.mk_prediction code_fadd fadd_dom [] (fadd_lemma code_fadd IA.win))

let fadd_ //: normal lowstar_add1_t
= as_normal_t #lowstar_fadd_t lowstar_fadd
