module Lib.IntTypes.Intrinsics

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul


val add_carry_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) -> 
  Stack uint64 
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 -> 
      modifies1 r h0 h1 /\ v c <= 1 /\
      (let r = Seq.index (as_seq h1 r) 0 in 
       v r + v c * pow2 64 == v x + v y + v cin))


val sub_borrow_u64: cin:uint64 -> x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) -> 
  Stack uint64
    (requires fun h -> live h r /\ v cin <= 1)
    (ensures  fun h0 c h1 -> 
      modifies1 r h0 h1 /\ 
      (let r = Seq.index (as_seq h1 r) 0 in 
       v r - v c * pow2 64 == v x - v y - v cin))
