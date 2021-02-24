module Lib.IntVector.Intrinsics

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

(* 128-bit Vector Intrinsics *)
val vec128 : Type0


val ni_aes_enc: vec128 -> vec128 -> vec128

val ni_aes_enc_last: vec128 -> vec128 -> vec128

val ni_aes_keygen_assist: vec128 -> uint8 -> vec128


val ni_clmul: vec128 -> vec128 -> uint8 -> vec128


val vec128_eq64: vec128 -> vec128 -> vec128


val vec128_eq32: vec128 -> vec128 -> vec128


val vec128_gt64: vec128 -> vec128 -> vec128


val vec128_gt32: vec128 -> vec128 -> vec128



val vec128_xor: vec128 -> vec128 -> vec128


val vec128_or: vec128 -> vec128 -> vec128

val vec128_and: vec128 -> vec128 -> vec128

val vec128_lognot: vec128 -> vec128

val vec128_shift_left: vec128 -> size_t -> vec128

val vec128_shift_right: vec128 -> size_t -> vec128

val vec128_shift_left64: vec128 -> size_t -> vec128

val vec128_shift_right64: vec128 -> size_t -> vec128

val vec128_shift_left32: vec128 -> size_t -> vec128

val vec128_shift_right32: vec128 -> size_t -> vec128

val vec128_rotate_right32: vec128 -> size_t -> vec128

val vec128_rotate_left32: vec128 -> size_t -> vec128

val vec128_shuffle32: vec128 -> size_t -> size_t -> size_t -> size_t -> vec128

val vec128_shuffle64: vec128 -> size_t -> size_t -> vec128


val vec128_rotate_right_lanes32: vec128 -> size_t -> vec128

val vec128_rotate_right_lanes64: vec128 -> size_t -> vec128


val vec128_load128: u:uint128 -> vec128


val vec128_load64: u:uint64 -> vec128


val vec128_load64s: lo:uint64 -> hi:uint64 -> vec128


val vec128_load32: u:uint32 -> vec128


val vec128_load32s: x0:uint32 -> x1:uint32 -> x2:uint32 -> x3:uint32 -> vec128


val vec128_load32_le: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

val vec128_load64_le: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

val vec128_load128_le: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

val vec128_load_be: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))


val vec128_load32_be: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))


val vec128_load64_be: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))


val vec128_store32_le: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

val vec128_store64_le: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

val vec128_store128_le: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

val vec128_store_be: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))


val vec128_store32_be: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))


val vec128_store64_be: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))


val vec128_insert8: vec128 -> uint8 -> size_t -> vec128


val vec128_insert32: vec128 -> uint32 -> size_t -> vec128


val vec128_insert64: vec128 -> uint64 -> size_t -> vec128


val vec128_extract8: vec128 -> size_t -> uint8


val vec128_extract32: vec128 -> size_t -> uint32


val vec128_extract64: vec128 -> size_t -> uint64


val vec128_zero: vec128


val vec128_interleave_low32: vec128 -> vec128 -> vec128


val vec128_interleave_high32: vec128 -> vec128 -> vec128


val vec128_interleave_low64: vec128 -> vec128 -> vec128


val vec128_interleave_high64: vec128 -> vec128 -> vec128


val vec128_add64: vec128 -> vec128 -> vec128


val vec128_sub64: vec128 -> vec128 -> vec128


val vec128_mul64: vec128 -> vec128 -> vec128


val vec128_smul64: vec128 -> uint64 -> vec128



val vec128_add32: vec128 -> vec128 -> vec128


val vec128_sub32: vec128 -> vec128 -> vec128


val vec128_mul32: vec128 -> vec128 -> vec128


val vec128_smul32: vec128 -> uint32 -> vec128

(* 256-bit Vector Intrinsics *)

val vec256 : Type0


val vec256_eq64: vec256 -> vec256 -> vec256


val vec256_eq32: vec256 -> vec256 -> vec256


val vec256_gt64: vec256 -> vec256 -> vec256


val vec256_gt32: vec256 -> vec256 -> vec256


val vec256_xor: vec256 -> vec256 -> vec256

val vec256_or: vec256 -> vec256 -> vec256

val vec256_and: vec256 -> vec256 -> vec256

val vec256_lognot: vec256 -> vec256

val vec256_shift_left: vec256 -> size_t -> vec256

val vec256_shift_right: vec256 -> size_t -> vec256

val vec256_shift_left64: vec256 -> size_t -> vec256

val vec256_shift_right64: vec256 -> size_t -> vec256

val vec256_shift_left32: vec256 -> size_t -> vec256

val vec256_shift_right32: vec256 -> size_t -> vec256

val vec256_rotate_left32: vec256 -> size_t -> vec256

val vec256_rotate_right32: vec256 -> size_t -> vec256

val vec256_rotate_right64: vec256 -> size_t -> vec256

val vec256_shuffle128: vec256 -> size_t -> size_t -> vec256

val vec256_shuffle64: vec256 -> size_t -> size_t -> size_t -> size_t -> vec256

val vec256_shuffle32: vec256 -> size_t -> size_t -> size_t -> size_t -> size_t -> size_t -> size_t -> size_t -> vec256


val vec256_rotate_right_lanes32: vec256 -> size_t -> vec256

val vec256_rotate_right_lanes64: vec256 -> size_t -> vec256

val vec256_rotate_right_lanes128: vec256 -> size_t -> vec256


val vec256_load64: x:uint64 -> vec256


val vec256_load64s: x0:uint64 -> x1:uint64 -> x2:uint64 -> x3:uint64 -> vec256


val vec256_load32: x:uint32 -> vec256


val vec256_load32s: x0:uint32 -> x1:uint32 ->  x2:uint32 -> x3:uint32 ->  x4:uint32 -> x5:uint32 ->  x6:uint32 -> x7:uint32 -> vec256


val vec256_load128: x:uint128 -> vec256


val vec256_load128s: x0:uint128 -> x1:uint128 -> vec256



val vec256_load32_le: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

val vec256_load64_le: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

val vec256_load128_le: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))


val vec256_load_be: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))


val vec256_store32_le: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

val vec256_store64_le: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

val vec256_store128_le: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))


val vec256_store_be: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))


val vec256_insert8: vec256 -> uint8 -> size_t -> vec256


val vec256_insert32: vec256 -> uint32 -> size_t -> vec256


val vec256_insert64: vec256 -> uint64 -> size_t -> vec256


val vec256_extract8: vec256 -> size_t -> uint8


val vec256_extract32: vec256 -> size_t -> uint32


val vec256_extract64: vec256 -> size_t -> uint64


val vec256_zero: vec256


val vec256_interleave_low32: vec256 -> vec256 -> vec256


val vec256_interleave_high32: vec256 -> vec256 -> vec256


val vec256_interleave_low64: vec256 -> vec256 -> vec256


val vec256_interleave_high64: vec256 -> vec256 -> vec256


val vec256_interleave_low128: vec256 -> vec256 -> vec256


val vec256_interleave_high128: vec256 -> vec256 -> vec256


val vec256_add64: vec256 -> vec256 -> vec256


val vec256_sub64: vec256 -> vec256 -> vec256


val vec256_mul64: vec256 -> vec256 -> vec256


val vec256_smul64: vec256 -> uint64 -> vec256


val vec256_add32: vec256 -> vec256 -> vec256


val vec256_sub32: vec256 -> vec256 -> vec256


val vec256_mul32: vec256 -> vec256 -> vec256


val vec256_smul32: vec256 -> uint32 -> vec256

 val bit_mask64: uint64 -> uint64
