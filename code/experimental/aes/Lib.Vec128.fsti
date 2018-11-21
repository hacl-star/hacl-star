module Lib.Vec128

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer


val vec128 : Type0

noextract
val ni_aes_enc: vec128 -> vec128 -> vec128
noextract
val ni_aes_enc_last: vec128 -> vec128 -> vec128
noextract
val ni_aes_keygen_assist: vec128 -> uint8 -> vec128

noextract
val ni_clmul: vec128 -> vec128 -> uint8 -> vec128

noextract
val vec128_eq64: vec128 -> vec128 -> vec128

noextract
val vec128_xor: vec128 -> vec128 -> vec128

noextract
val vec128_or: vec128 -> vec128 -> vec128
noextract
val vec128_and: vec128 -> vec128 -> vec128
noextract
val vec128_lognot: vec128 -> vec128
noextract
val vec128_shift_left: vec128 -> size_t -> vec128
noextract
val vec128_shift_right: vec128 -> size_t -> vec128
noextract
val vec128_shift_left64: vec128 -> size_t -> vec128
noextract
val vec128_shift_right64: vec128 -> size_t -> vec128
noextract
val vec128_shuffle32: vec128 -> uint8 -> vec128
noextract
val vec128_shuffle32_spec: uint8 -> uint8 -> uint8 -> uint8 -> uint8

noextract
val vec128_load64: u:uint64 -> vec128

noextract
val vec128_load64s: hi:uint64 -> lo:uint64 -> vec128

noextract
val vec128_load_le: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

noextract
val vec128_load_be: b:lbuffer uint8 16ul -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))
			   
noextract
val vec128_store_le: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

noextract
val vec128_store_be: b:lbuffer uint8 16ul -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc b) h0 h1))

noextract
val vec128_insert32: vec128 -> uint32 -> uint8 -> vec128
noextract
val vec128_zero: vec128

noextract
val vec128_interleave_low64: vec128 -> vec128 -> vec128

noextract
val vec128_interleave_high64: vec128 -> vec128 -> vec128

noextract
val vec128_smul64: vec128 -> uint64 -> vec128

noextract
val vec128_mul64: vec128 -> vec128 -> vec128

noextract
val vec128_add64: vec128 -> vec128 -> vec128
noextract
val vec128_sub64: vec128 -> vec128 -> vec128

noextract val bit_mask64: uint64 -> uint64
