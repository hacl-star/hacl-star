module Lib.RawBuffer

friend Lib.IntTypes

open LowStar.Buffer

open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open Lib.IntTypes

let blit src idx_src dst idx_dst len =
  let h0 = get () in
  blit src idx_src dst idx_dst len;
  let h1 = get () in
  assert (forall (i:nat). i < U32.v len ==>
      Seq.index (as_seq h1 dst) (U32.v idx_dst + i) ==
      Seq.index (Seq.slice (as_seq h1 dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len)) i)

let lbytes_eq #n b1 b2 =
  let open LowStar.BufferOps in
  let h0 = get() in
  let inv h i b =
    modifies loc_none h0 h /\
    i <= U32.v n /\
    (if b then 
       0 < i /\ Seq.index (as_seq h0 b1) (i-1) <> Seq.index (as_seq h0 b2) (i-1)
     else
       forall (j:nat).j < i ==> Seq.index (as_seq h0 b1) j == Seq.index (as_seq h0 b2) j)
  in
  let _, b = C.Loops.interruptible_for 0ul n inv (fun i -> b1.(i) <> b2.(i)) in
  not b
