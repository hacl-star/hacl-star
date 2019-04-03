module Hacl.UInt32x4N

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open C.Loops
open FStar.Seq

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t
assume new type vec
assume val vec_size: (x:u32{U32.v x % 4 = 0})
assume val vec_as_seq: vec -> GTot (s:seq h32{length s == U32.v vec_size})
assume val vec_load_le: b:uint8_p -> ST vec 
              (requires (fun h -> live h b /\ Buffer.length b == 32))
	      (ensures  (fun h0 r h1 -> live h1 b /\ modifies_0 h0 h1 /\  
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h0 b) in
			     s == vec_as_seq r)))
assume val vec_store_le: b:uint8_p -> r:vec -> ST unit
              (requires (fun h -> live h b /\ Buffer.length b == 32))
	      (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\	
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h1 b) in
			     s == vec_as_seq r)))

assume val vec_load128_le: b:uint8_p -> ST vec 
              (requires (fun h -> live h b /\ Buffer.length b == 16))
	      (ensures  (fun h0 r h1 -> live h1 b /\ modifies_0 h0 h1 /\  
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h0 b) in
			     let rs = vec_as_seq r in
			     forall i. (0 <= i /\ i < U32.v vec_size) ==>
			     index rs i = index s (i % 4))))

assume val vec_load_32: h32-> Tot vec
assume val vec_load_32x4: h32 -> h32 -> h32 -> h32 -> Tot vec
assume val vec_load_32x8: h32 -> h32 -> h32 -> h32 -> h32 -> h32 -> h32 -> h32 -> Tot vec
assume val vec_shuffle_right: vec -> r:u32 -> Tot (vec)
assume val vec_rotate_left:  vec -> r:u32 -> Tot (vec)
assume val vec_rotate_left_8:  vec -> Tot (vec)
assume val vec_rotate_left_16:  vec -> Tot (vec)
assume val vec_add:  vec -> vec -> Tot (vec)
assume val vec_xor:  vec -> vec -> Tot (vec)

assume val vec_interleave32_low: vec -> vec -> Tot vec
assume val vec_interleave32_high: vec -> vec -> Tot vec
assume val vec_interleave64_low: vec -> vec -> Tot vec
assume val vec_interleave64_high: vec -> vec -> Tot vec
assume val vec_choose_128: vec -> vec -> u32 -> u32 -> Tot vec

inline_for_extraction let op_Less_Less_Less (v:vec) (r:u32): Tot (vec) = vec_rotate_left v r
inline_for_extraction let op_Plus_Percent_Hat (v1:vec) (v2:vec): Tot (vec) = vec_add v1 v2
inline_for_extraction let op_Hat_Hat (v1:vec) (v2:vec): Tot (vec) = vec_xor v1 v2

assume val zero:  vec
assume val one_le:  vec
assume val two_le:  vec

