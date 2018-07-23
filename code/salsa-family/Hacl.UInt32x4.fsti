module Hacl.UInt32x4

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Seq

open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness

open Spec.Loops

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

val vec: Type0

#reset-options "--max_fuel 0"

let vec_size = 4ul

val vec_as_seq: vec -> GTot Spec.Chacha20_vec.vec

val vec_load_le: b:uint8_p{Buffer.length b = 16} -> Stack vec
              (requires (fun h -> live h b))
	      (ensures  (fun h0 r h1 -> live h1 b /\ h0 == h1 /\ live h0 b /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h0 b)) in
			     s == vec_as_seq r)))


val vec_store_le: b:uint8_p{Buffer.length b = 16} -> r:vec -> Stack unit
              (requires (fun h -> live h b))
	      (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h1 b)) in
			     s == vec_as_seq r)))


val vec_load128_le: b:uint8_p{Buffer.length b = 16} -> Stack vec 
              (requires (fun h -> live h b))
	      (ensures  (fun h0 r h1 -> live h1 b /\ h0 == h1 /\ live h0 b /\
	      		    (let s = Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h0 b)) in
			     let rs = vec_as_seq r in rs == s)))

val vec_load_32x4: x1:h32 -> x2:h32 -> x3:h32 -> x4:h32 -> Tot (s:vec{vec_as_seq s == reveal_h32s (Seq.Create.create_4 x1 x2 x3 x4)})
val vec_shuffle_right: s0:vec -> r:u32{U32.v r < 4} -> Tot (s1:vec{vec_as_seq s1 == Spec.Chacha20_vec.shuffle_right (vec_as_seq s0) (U32.v r)})
val vec_rotate_left: s0:vec -> r:u32{U32.v r < 32} -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) r})
val vec_rotate_left_8: s0:vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) 8ul})
val vec_rotate_left_16: s0:vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Less_Less_Less (vec_as_seq s0) 16ul})
val vec_add: s0:vec -> s0':vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Plus_Percent_Hat (vec_as_seq s0) (vec_as_seq s0')})
val vec_xor: s0:vec -> s0':vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Hat_Hat (vec_as_seq s0) (vec_as_seq s0')})

private val zero:  zero:vec{vec_as_seq zero == Seq.Create.create_4 0ul 0ul 0ul 0ul}
private val one_le:  one:vec{vec_as_seq one == Seq.Create.create_4 1ul 0ul 0ul 0ul}
private val two_le:  two:vec{vec_as_seq two == Seq.Create.create_4 2ul 0ul 0ul 0ul}

val vec_increment: s0:vec -> Tot (s1:vec{
  vec_as_seq s1 == Spec.Chacha20_vec.op_Plus_Percent_Hat (vec_as_seq s0) (vec_as_seq one_le)})

val vec_zero: unit -> Tot (s1:vec{vec_as_seq s1 == vec_as_seq zero})

inline_for_extraction let ( <<< ) (v:vec) (r:u32{U32.v r < 32}): Tot (vec) = vec_rotate_left v r
inline_for_extraction let ( +%^ ) (v1:vec) (v2:vec): Tot (vec) = vec_add v1 v2
inline_for_extraction let ( ^^ ) (v1:vec) (v2:vec): Tot (vec) = vec_xor v1 v2

