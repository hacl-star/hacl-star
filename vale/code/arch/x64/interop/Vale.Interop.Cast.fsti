module Vale.Interop.Cast

module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open FStar.HyperStack.ST

open Interop.Base
open Vale.AsLowStar.MemoryHelpers

open FStar.Mul

unfold
let b_t (t:base_typ) = b:B.buffer (base_typ_as_type t)

val copy_down (#t:base_typ) (b:b_t t) (b8:b_t TUInt8) : Stack unit
  (requires fun h -> B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * view_n t)
  (ensures fun h0 _ h -> 
    B.live h b /\ B.live h b8 /\ 
    B.modifies (B.loc_buffer b8) h0 h /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h0 b) i == low_buffer_read t h b8 i))

val copy_up (#t:base_typ) (b:b_t t) (b8:b_t TUInt8) : Stack unit
  (requires fun h -> B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * view_n t)
  (ensures fun h0 _ h1 -> 
    B.live h1 b /\ B.live h0 b8 /\ B.modifies (B.loc_buffer b) h0 h1 /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h1 b) i == low_buffer_read t h0 b8 i))

val imm_copy_up (#t:base_typ) (b:b_t t) (b8:b_t TUInt8) : Stack unit
  (requires fun h -> B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * view_n t /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h b) i == low_buffer_read t h b8 i))
  (ensures fun h0 _ h -> h0 == h) 
