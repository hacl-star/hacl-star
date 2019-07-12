module Interop_assumptions

open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open X64.Machine_s

assume val st_put (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0) (fun h0 _ h1 -> f h0 == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32
