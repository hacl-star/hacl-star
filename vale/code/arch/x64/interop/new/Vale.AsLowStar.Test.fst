module Vale.AsLowStar.Test
open Interop.Base
module ME = X64.Memory
module IA = Interop.Assumptions
module V = X64.Vale.Decls
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module W = Vale.AsLowStar.Wrapper

[@__reduce__] unfold
let t = TD_Buffer ME.TUInt64

[@__reduce__] unfold
let dom : (x:list td {List.length x == 2}) =
  let y = [t;t] in
  assert_norm (List.length y = 2);
  y

assume val pre : VSig.vale_pre dom
assume val post : VSig.vale_post dom
assume val n : nat
assume val v: VSig.vale_sig pre post
assume val c: V.va_code

[@__reduce__]
let call_c_t = IX64.as_lowstar_sig_t_weak c dom [] _ _ (W.mk_prediction c dom [] n (v c IA.win))
let call_c : call_c_t = IX64.wrap_weak c dom (W.mk_prediction c dom [] n (v c IA.win))
