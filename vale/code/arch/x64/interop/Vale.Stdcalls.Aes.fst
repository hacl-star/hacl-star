module Vale.Stdcalls.Aes

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

let lowstar_key128 : lowstar_key128_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_key128
    dom
    (W.mk_prediction code_key128 dom [] (key128_lemma code_key128 IA.win))

let aes128_key_expansion //: normal lowstar_key128_t
  = as_normal_t #lowstar_key128_t lowstar_key128

let lowstar_key256 : lowstar_key256_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_key256
    dom
    (W.mk_prediction code_key256 dom [] (key256_lemma code_key256 IA.win))

let aes256_key_expansion //: normal lowstar_key256_t
  = as_normal_t #lowstar_key256_t lowstar_key256
