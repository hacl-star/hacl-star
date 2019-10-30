module Vale.Interop.Assumptions
open FStar.Mul
open Vale.Interop.Base
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module MS = Vale.X64.Machine_s

assume
val st_put
      (#a:Type)
      (p:HS.mem -> Type0)
      (f:(h0:HS.mem{p h0} ->
           GTot (x:(a & HS.mem){ST.equal_domains h0 (snd x)})))
  : ST.Stack a
    (requires p)
    (ensures fun h0 x h1 -> f h0 == (x,h1))

//The initial registers, xmms, flags
assume
val init_regs: (regs:(MS.reg_64 -> MS.nat64){regs MS.rRsp >= 4096})

assume
val init_xmms: MS.reg_xmm -> MS.quad32

assume
val init_flags: MS.flag -> option bool

// Abstract current operating system from Low*
assume
val win: bool
