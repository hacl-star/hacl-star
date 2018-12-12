module Lib.Vec256

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

val vec256 : Type0

noextract
val vec256_eq64: vec256 -> vec256 -> vec256
noextract
val vec256_xor: vec256 -> vec256 -> vec256
noextract
val vec256_or: vec256 -> vec256 -> vec256
noextract
val vec256_and: vec256 -> vec256 -> vec256
noextract
val vec256_lognot: vec256 -> vec256
noextract
val vec256_shift_left: vec256 -> size_t -> vec256
noextract
val vec256_shift_right: vec256 -> size_t -> vec256
noextract
val vec256_shift_left64: vec256 -> size_t -> vec256
noextract
val vec256_shift_right64: vec256 -> size_t -> vec256
noextract
val vec256_shuffle64: vec256 -> uint8 -> vec256
noextract
val vec256_shuffle64_spec: uint8 -> uint8 -> uint8 -> uint8 -> uint8

noextract
val vec256_load64: x:uint64 -> vec256

noextract
val vec256_load64s: lo:uint64 -> hi:uint64 -> lo2:uint64 -> hi2:uint64 -> vec256

noextract
val vec256_load_le: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

noextract
val vec256_load_be: b:lbuffer uint8 32ul -> ST vec256
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))
			   
noextract
val vec256_store_le: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

noextract
val vec256_store_be: b:lbuffer uint8 32ul -> vec256 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

noextract
val vec256_insert32: vec256 -> uint32 -> uint8 -> vec256

noextract
val vec256_zero: vec256

noextract
val vec256_interleave_low64: vec256 -> vec256 -> vec256

noextract
val vec256_interleave_high64: vec256 -> vec256 -> vec256

noextract
val vec256_interleave_low128: vec256 -> vec256 -> vec256

noextract
val vec256_interleave_high128: vec256 -> vec256 -> vec256

noextract
val vec256_smul64: vec256 -> uint64 -> vec256

noextract
val vec256_mul64: vec256 -> vec256 -> vec256

noextract
val vec256_add64: vec256 -> vec256 -> vec256
noextract
val vec256_sub64: vec256 -> vec256 -> vec256

noextract val bit_mask64: uint64 -> uint64
