module Lib.Utils

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer

type lbuffer a len = b:buffer a{length b == len}
type bytes = buffer FStar.UInt8.t
type lbytes l = b:bytes {length b == l} 

inline_for_extraction 
val blit: #a:Type -> src:buffer a -> start1:size_t -> dst:buffer a -> start2:size_t -> len:size_t -> ST unit
               (requires (fun h -> live h src /\ live h dst)) (ensures (fun h0 _ h1 -> live h1 src /\ live h1 dst /\ modifies (loc_buffer dst) h0 h1))
let blit #a src start1 dst start2 len = 
    blit src (Lib.RawIntTypes.size_to_UInt32 start1) dst (Lib.RawIntTypes.size_to_UInt32 start2) (Lib.RawIntTypes.size_to_UInt32 len) 

inline_for_extraction
let htobe32 (u:uint32) = Lib.RawIntTypes.u32_from_UInt32 (C.Endianness.htobe32 (Lib.RawIntTypes.u32_to_UInt32 u))

inline_for_extraction 
val load64_le: b:lbytes 8 -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_le b = 
    let u = C.Endianness.load64_le b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_le: b:lbytes 8 -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_le b u = 
    C.Endianness.store64_le b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction 
val load64_be: b:lbytes 8 -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_be b = 
    let u = C.Endianness.load64_be b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_be: b:lbytes 8 -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_be b u = 
    C.Endianness.store64_be b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction 
val store32_be: b:lbytes 4 -> u:uint32 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store32_be b u = 
    C.Endianness.store32_be b (Lib.RawIntTypes.u32_to_UInt32 u)

inline_for_extraction 
val gcreateL: #a:Type -> l:list a -> ST (buffer a)
	      (requires (fun h -> True))
	      (ensures (fun h0 b h1 -> recallable b /\ length b == List.Tot.length l))
let gcreateL #a l = 
    gcmalloc_of_list FStar.HyperStack.root l


inline_for_extraction
val sub: #a:Type -> b:buffer a -> i:size_t -> j:size_t -> ST (buffer a) 
         (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let sub #a b i j = Lib.RawIntTypes.(sub b (size_to_UInt32 i) (size_to_UInt32 j))

inline_for_extraction 
val loop_nospec: #h0:mem -> #a:Type -> n:size_t -> buf:buffer a -> 
		 impl:(size_t -> ST unit (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1 /\ live h1 buf))) -> ST unit 
         (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> live h1 buf /\ modifies (loc_buffer buf) h0 h1))
inline_for_extraction 
let loop_nospec #h0 #a (n:size_t) (buf:buffer a) impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:UInt32.t{0 <= UInt32.v j /\ UInt32.v j <= size_v n}) : Stack unit
      (requires (fun h -> inv h (UInt32.v j)))
      (ensures (fun h1 _ h2 -> inv h2 (UInt32.v j + 1))) =
      impl (Lib.RawIntTypes.size_from_UInt32 j) in
  C.Loops.for 0ul (Lib.RawIntTypes.size_to_UInt32 n) inv f'

inline_for_extraction
let op_Array_Assignment #a #b #c buf i v = upd #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i) v
inline_for_extraction
let op_Array_Access #a #b #c buf i  = index #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i)
