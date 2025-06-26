module Vale.Stdcalls.X64.Aes

open FStar.Mul
open FStar.HyperStack.ST
open Vale.Def.Types_s

open Vale.Interop.Base
module IX64 = Vale.Interop.X64
module IA = Vale.Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters

let lowstar_key128 : lowstar_key128_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_key128
    dom
    (W.mk_prediction code_key128 dom [] (key128_lemma code_key128 IA.win))

let aes128_key_expansion //: normal lowstar_key128_t
  = as_normal_t #lowstar_key128_t lowstar_key128

let lowstar_key256 : lowstar_key256_t =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_key256
    dom
    (W.mk_prediction code_key256 dom [] (key256_lemma code_key256 IA.win))

let aes256_key_expansion //: normal lowstar_key256_t
  = as_normal_t #lowstar_key256_t lowstar_key256
