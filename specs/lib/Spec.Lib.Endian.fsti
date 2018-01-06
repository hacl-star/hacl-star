module Spec.Lib.Endian

open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.HyperStack.ST

inline_for_extraction
val uint32_from_bytes_le: i:lbuffer uint8 4 -> Stack uint32 
			 (requires (fun h -> live h i))
			 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

inline_for_extraction
val uint64_from_bytes_be: i:lbuffer uint8 8 -> Stack uint64 
			 (requires (fun h -> live h i))
			 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))

inline_for_extraction
val uint64_to_bytes_be: i:lbuffer uint8 8 -> uint64 -> Stack unit
			(requires (fun h -> live h i))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
 

