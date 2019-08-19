module Lib.RawBuffer

friend Lib.IntTypes

open LowStar.Buffer

open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open Lib.IntTypes

let uint32_t = U32.t

let blit src idx_src dst idx_dst len =
  let h0 = get () in
  blit src idx_src dst idx_dst len;
  let h1 = get () in
  assert (forall (i:nat). i < U32.v len ==>
      Seq.index (as_seq h1 dst) (U32.v idx_dst + i) ==
      Seq.index (Seq.slice (as_seq h1 dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len)) i)
