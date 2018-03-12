module Spec.Lib.Endian

open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.HyperStack.ST

inline_for_extraction
val uint32_from_bytes_le: i:lbuffer uint8 4 -> Stack uint32
			 (requires (fun h -> live h i))
			 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

inline_for_extraction
val uint32_to_bytes_le: o:lbuffer uint8 4 -> uint32 -> Stack unit
			 (requires (fun h -> live h o))
			 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 o h0 h1))
