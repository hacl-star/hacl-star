module Vale.Stdcalls.GCMencrypt

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


(* And here's the gcm wrapper itself *)
let lowstar_gcm128 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gcm128_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_gcm128
    224
    dom
    (W.mk_prediction code_gcm128 dom [] ((gcm128_lemma s) code_gcm128 IA.win))

#push-options "--lax"

let gcm128_encrypt //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128_t s)
  = admit()
// TODO: This should be trivial, but F* loops forever and ends up crashing when running out of memory
// as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm128 s)

#pop-options

(* And here's the gcm wrapper itself *)
let lowstar_gcm256 (s:Ghost.erased (Seq.seq nat32)) : lowstar_gcm256_t s =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 20);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_gcm256
    224
    dom
    (W.mk_prediction code_gcm256 dom [] ((gcm256_lemma s) code_gcm256 IA.win))

#push-options "--lax"

let gcm256_encrypt //: normal ((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256_t s)
  =
  admit()
// TODO: Same as above
//  as_normal_t #((s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256_t s) (fun (s:Ghost.erased (Seq.seq nat32)) -> lowstar_gcm256 s)

#pop-options
