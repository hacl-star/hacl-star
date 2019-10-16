module Lib.RawBuffer

open FStar.HyperStack.ST

open LowStar.Buffer
open Lib.IntTypes

module U8 = FStar.UInt8
module U32 = FStar.UInt32

inline_for_extraction noextract
val blit: src:buffer U8.t -> idx_src:U32.t -> dst:buffer uint8 -> idx_dst:U32.t -> len:U32.t -> ST unit
  (requires  fun h -> 
    live h src /\ live h dst /\ 
    U32.v idx_src + U32.v len <= length src /\
    U32.v idx_dst + U32.v len <= length dst /\
    disjoint src dst)
  (ensures   fun h0 _ h1 -> 
    modifies (loc_buffer dst) h0 h1 /\
    live h1 dst /\
    (forall (i:nat). i < U32.v len ==>
      Seq.index (as_seq h1 dst) (U32.v idx_dst + i) ==
      Lib.RawIntTypes.u8_from_UInt8 (Seq.index (as_seq h0 src) (U32.v idx_src + i))) /\
    Seq.slice (as_seq h1 dst) 0 (U32.v idx_dst) ==
    Seq.slice (as_seq h0 dst) 0 (U32.v idx_dst) /\
    Seq.slice (as_seq h1 dst) (U32.v idx_dst + U32.v len) (length dst) ==
    Seq.slice (as_seq h0 dst) (U32.v idx_dst + U32.v len) (length dst))

inline_for_extraction noextract
val lbytes_eq: #n:size_t -> b1:buffer uint8 -> b2:buffer uint8 -> Stack bool
  (requires fun h -> len b1 == n /\ len b2 == n /\ live h b1 /\ live h b2)
  (ensures  fun h0 r h1 -> 
    modifies loc_none h0 h1 /\ 
    (r <==> Seq.equal (as_seq h0 b1) (as_seq h0 b2)))
