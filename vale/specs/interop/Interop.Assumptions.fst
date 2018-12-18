module Interop.Assumptions
open Interop.Base
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module MS = X64.Machine_s

assume
val st_put
      (#a:Type)
      (p:HS.mem -> Type0)
      (f:(h0:HS.mem{p h0} ->
           GTot (x:(a & HS.mem){ST.equal_domains h0 (snd x)})))
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
assume
val win: bool

(* If two refs have the same address, and are in the heap, they are equal *)
assume
val ref_extensionality
      (#a:Type0)
      (#rel:Preorder.preorder a)
      (h:Heap.heap)
      (r1 r2:Heap.mref a rel)
  : Lemma
     (ensures Heap.contains h r1 /\
              Heap.contains h r2 /\
              Heap.addr_of r1 = Heap.addr_of r2 ==>
              r1 == r2)

