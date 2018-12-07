module Vale.AsLowStar.Wrapper
open Vale.AsLowStar.Signature
open Vale.AsLowStar.Util
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module IA = Interop_assumptions
module IS = X64.Interop_s
module ME = X64.Memory
module MS = X64.Machine_s
module V = X64.Vale.Decls
module VS = X64.Vale.State
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig

val wrap
    (code:V.va_code)
    (dom:sig_arity_ok)
    (num_stack_slots:nat)
    (pre:VSig.vale_pre dom)
    (post:VSig.vale_post dom)
    (v:VSig.vale_sig pre post)
  : LSig.as_lowstar_sig code dom num_stack_slots pre post
