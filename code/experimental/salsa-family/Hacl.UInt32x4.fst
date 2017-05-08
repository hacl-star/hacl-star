module Hacl.UInt32x4


open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Seq

open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness

open C.Loops

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type vec = Spec.Chacha20_vec.vec

#reset-options "--max_fuel 0"

val vec_size: (x:u32{U32.v x % 4 = 0})
let vec_size =
  assert_norm (4 % 4 = 0); 4ul

val vec_as_seq: vec -> GTot (s:seq h32{length s == U32.v vec_size})
let vec_as_seq vec =
  vec

assume val vec_load_le: b:uint8_p{Buffer.length b = 16} -> Stack vec
              (requires (fun h -> live h b))
	      (ensures  (fun h0 r h1 -> live h1 b /\ h0 == h1 /\ live h0 b /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h0 b) in
			     s == vec_as_seq r)))


assume val vec_store_le: b:uint8_p{Buffer.length b = 16} -> r:vec -> Stack unit
              (requires (fun h -> live h b))
	      (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h1 b) in
			     s == vec_as_seq r)))


assume val vec_load128_le: b:uint8_p{Buffer.length b = 16} -> Stack vec 
              (requires (fun h -> live h b))
	      (ensures  (fun h0 r h1 -> live h1 b /\ h0 == h1 /\ live h0 b /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (as_seq h0 b) in
			     let rs = vec_as_seq r in rs == s)))

(* assume val vec_load_32: h32-> Tot vec *)

assume val vec_load_32x4: x1:h32 -> x2:h32 -> x3:h32 -> x4:h32 -> Tot (s:vec{vec_as_seq s == Seq.Create.create_4 x1 x2 x3 x4})
assume val vec_load_32x8: x1:h32 -> x2:h32 -> x3:h32 -> x4:h32 -> h32 -> h32 -> h32 -> h32 -> Tot (s:vec{vec_as_seq s == Seq.Create.create_4 x1 x2 x3 x4})
assume val vec_shuffle_right: s0:vec -> r:u32{U32.v r < 4} -> Tot (s1:vec{vec_as_seq s1 == Spec.Chacha20_vec.shuffle_right (vec_as_seq s0) (U32.v r)})
assume val vec_rotate_left: s0:vec -> r:u32{U32.v r < 32} -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) r})
assume val vec_rotate_left_8: s0:vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) 8ul})
assume val vec_rotate_left_8: s0:vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) 16ul})
assume val vec_add: s0:vec -> s0':vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Plus_Percent_Hat (vec_as_seq s0) (vec_as_seq s0')})
assume val vec_xor: s0:vec -> s0':vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Hat_Hat (vec_as_seq s0) (vec_as_seq s0')})

(* assume val vec_interleave32_low: vec -> vec -> Tot vec *)
(* assume val vec_interleave32_high: vec -> vec -> Tot vec *)
(* assume val vec_interleave64_low: vec -> vec -> Tot vec *)
(* assume val vec_interleave64_high: vec -> vec -> Tot vec *)

val vec_choose_128: v:vec -> vec -> u32 -> u32 -> Tot (v':vec{v' == v})

inline_for_extraction let op_Less_Less_Less (v:vec) (r:u32{U32.v r < 32}): Tot (vec) = vec_rotate_left v r
inline_for_extraction let op_Plus_Percent_Hat (v1:vec) (v2:vec): Tot (vec) = vec_add v1 v2
inline_for_extraction let op_Hat_Hat (v1:vec) (v2:vec): Tot (vec) = vec_xor v1 v2

assume val zero:  zero:vec{vec_as_seq zero == Seq.Create.create_4 0ul 0ul 0ul 0ul}
assume val one_le:  one:vec{vec_as_seq one == Seq.Create.create_4 1ul 0ul 0ul 0ul}
assume val two_le:  two:vec{vec_as_seq two == Seq.Create.create_4 2ul 0ul 0ul 0ul}
