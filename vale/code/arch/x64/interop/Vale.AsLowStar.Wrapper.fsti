module Vale.AsLowStar.Wrapper
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module LU = LowStar.Util
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig

val lowstar_lemma
          (dom:IX64.arity_ok td)
          (code:V.va_code)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre dom)
          (post:VSig.vale_post dom)
          (v:VSig.vale_sig pre post)
    : LSig.lowstar_lemma_typ #dom code [] num_stack_slots (pre code) (post code)
