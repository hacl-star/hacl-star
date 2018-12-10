module Interop.Assumptions
open Interop.Base
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module MS = X64.Machine_s
// module TS = X64.Taint_Semantics_s
// module BS = X64.Bytes_Semantics_s

assume 
val st_put (#a:Type) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot (a & HS.mem))
  : ST.Stack a 
    (requires p)
    (ensures fun h0 x h1 -> f h0 == (x,h1))

//The map from buffers to addresses in the heap, that remains abstract
assume 
val addrs: addr_map

//The initial registers and xmms
assume 
val init_regs: MS.reg -> MS.nat64

assume 
val init_xmms: MS.xmm -> MS.quad32

// Abstract current operating system from Low*
assume val win: bool
