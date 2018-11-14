module Lib.Utils

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer

unfold type lbuffer a len = b:buffer a{length b == len}
unfold type bytes = buffer FStar.UInt8.t
unfold type lbytes l = b:bytes {length b == l} 

inline_for_extraction 
val blit: #a:Type -> src:buffer a -> start1:size_t -> dst:buffer a -> start2:size_t -> len:size_t -> ST unit
               (requires (fun h -> live h src /\ live h dst)) (ensures (fun h0 _ h1 -> live h1 src /\ live h1 dst /\ modifies (loc_buffer dst) h0 h1))
let blit #a src start1 dst start2 len = 
    blit src (Lib.RawIntTypes.size_to_UInt32 start1) dst (Lib.RawIntTypes.size_to_UInt32 start2) (Lib.RawIntTypes.size_to_UInt32 len) 

inline_for_extraction
let htobe32 (u:uint32) = Lib.RawIntTypes.u32_from_UInt32 (C.Endianness.htobe32 (Lib.RawIntTypes.u32_to_UInt32 u))

inline_for_extraction 
val load32_le: b:bytes{length b == 4} -> ST uint32
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load32_le b = 
    let u = C.Endianness.load32_le b in
    Lib.RawIntTypes.u32_from_UInt32 u

inline_for_extraction 
val store32_le: b:bytes{length b == 4} -> u:uint32 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store32_le b u = 
    C.Endianness.store32_le b (Lib.RawIntTypes.u32_to_UInt32 u)
inline_for_extraction 
val load64_le: b:bytes{length b == 8} -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_le b = 
    let u = C.Endianness.load64_le b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_le: b:bytes{length b == 8} -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_le b u = 
    C.Endianness.store64_le b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction 
val load128_le: b:bytes{length b == 16} -> ST uint128
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load128_le b = 
    let u = C.Endianness.load128_le b in
    Lib.RawIntTypes.u128_from_UInt128 u

inline_for_extraction 
val store128_le: b:bytes{length b == 16} -> u:uint128 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store128_le b u = 
    C.Endianness.store128_le b (Lib.RawIntTypes.u128_to_UInt128 u)

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
val sub: #a:Type -> b:buffer a -> i:size_t -> j:size_t -> ST (b:buffer a{length b == size_v j}) 
         (requires (fun h -> live h b)) (ensures (fun h0 s h1 -> h0 == h1 /\ s == Lib.RawIntTypes.(gsub b (size_to_UInt32 i) (size_to_UInt32 j))))
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

inline_for_extraction
let op_String_Assignment #a buf i v = FStar.Seq.upd #a buf (Lib.RawIntTypes.uint_to_nat #U32 #SEC i) v
inline_for_extraction
let op_String_Access #a buf i = FStar.Seq.index #a buf (Lib.RawIntTypes.uint_to_nat #U32 #SEC i) 

inline_for_extraction
let create z i = alloca z (Lib.RawIntTypes.size_to_UInt32 i)

val size_v_size: n:size_nat -> Lemma 
                (requires True)
		(ensures (size_v (size n) == n))
		[SMTPat [size_v (size n)]]
let size_v_size n = ()

inline_for_extraction
val load64x2_le: b:lbytes 16 -> Stack (uint64 * uint64)
                   (requires (fun h -> live h b))
		   (ensures (fun h0 _ h1 -> h0 == h1))
let load64x2_le b = 
    let lo = load64_le (sub b (size 0) (size 8)) in
    let hi = load64_le (sub b (size 8) (size 8)) in
    (lo,hi)

inline_for_extraction
val store64x2_le: b:lbytes 16 -> lo:uint64 -> hi:uint64 -> Stack unit
                   (requires (fun h -> live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
let store64x2_le b lo hi = 
    store64_le (sub b (size 0) (size 8)) lo;
    store64_le (sub b (size 8) (size 8)) hi


let uint64_eq_mask (a:uint64) (b:uint64) : uint64
  = let x = a ^. b in
    let minus_x = (lognot x) +. (u64 1) in
    let x_or_minus_x = x |. minus_x in
    let xnx = x_or_minus_x >>. (u32 63) in
    let c = xnx -. (u64 1) in
    c

let uint64_gte_mask (a:uint64) (b:uint64) : uint64
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = x -. y in
    let x_sub_y_xor_y = x_sub_y ^. y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q (u32 63) in
    let c = sub_mod x_xor_q_ (u64 1) in
    c

let uint32_eq_mask (a:uint32) (b:uint32) : uint32
  = let x = a ^. b in
    let minus_x = (lognot x) +. (u32 1) in
    let x_or_minus_x = x |. minus_x in
    let xnx = x_or_minus_x >>. (u32 31) in
    let c = xnx -. (u32 1) in
    c

let uint32_gte_mask (a:uint32) (b:uint32) : uint32
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = x -. y in
    let x_sub_y_xor_y = x_sub_y ^. y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q (u32 31) in
    let c = sub_mod x_xor_q_ (u32 1) in
    c

inline_for_extraction
val uint32s_from_bytes_le: out:buffer uint32 -> b:bytes -> len:size_t{size_v len == length out} -> Stack unit
                   (requires (fun h -> live h b /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let uint32s_from_bytes_le out b len = 
    let h0 = ST.get () in
    loop_nospec #h0 len out 
      (fun i -> out.(i) <- load32_le (sub b (i *. size 4) (size 4)))

inline_for_extraction
val uint32s_to_bytes_le: out:bytes -> b:buffer uint32 -> len:size_t{size_v len == length b} -> Stack unit
                   (requires (fun h -> live h b /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let uint32s_to_bytes_le out b len = 
    let h0 = ST.get () in
    loop_nospec #h0 len out 
      (fun i -> store32_le (sub out (i *. size 4) (size 4)) b.(i))
      
