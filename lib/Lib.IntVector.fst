module Lib.IntVector

open FStar.Mul
module Ints = Lib.IntTypes
open Lib.IntVector.Intrinsics

// WARNING: this file is experimental and the vectorized implementations are
// currently not enabled on EverCrypt release builds.

#set-options "--admit_smt_queries true"

inline_for_extraction
let vec_t t w =
  match t,w with
  | U128, 1 -> vec128
  | t, 1 -> uint_t t SEC
  | U8,16 -> vec128
  | U64,2 -> vec128
  | U32,4 -> vec128
  | U128,2 -> vec256
  | U8,32 -> vec256
  | U32,8 -> vec256
  | U64,4 -> vec256
  | _,_ -> admit()

let vec_v #t #w x = admit()

let vec_zero (t:v_inttype) (w:width) =
  match t,w with
  | U128,1 -> vec128_zero
  | _,1 -> nat_to_uint #t #SEC 0
  | U8, 16
  | U32,4
  | U64,2 -> vec128_zero
  | U8, 32
  | U32,8
  | U64,4
  | U128,2 -> vec256_zero

let vec_counter (t:v_inttype) (w:width) =
  match t,w with
  | U128,1 -> vec128_zero
  | _,1 -> nat_to_uint #t #SEC 0
  | U32,4 -> vec128_load32s (u32 3) (u32 2) (u32 1) (u32 0)
  | U64,2 -> vec128_load64s (u64 1) (u64 0)
  | U32,8 -> vec256_load32s (u32 7) (u32 6) (u32 5) (u32 4) (u32 3) (u32 2) (u32 1) (u32 0)
  | U64,4 -> vec256_load64s (u64 3) (u64 2) (u64 1) (u64 0)
  | U128,2 -> vec256_load128s (u128 1) (u128 0)

let create2 #a x0 x1 = admit()
let create4 #a x0 x1 x2 x3 = admit()
let create8 #a x0 x1 x2 x3 x4 x5 x6 x7 = admit()
let create16 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = admit()
let create32 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15  = admit()

let vec_load (#t:v_inttype) (x:uint_t t SEC) (w:width) =
  match t,w with
  | U128,1 -> vec128_load128 x
  | _,1 -> x
  | U32,4 -> vec128_load32 x
  | U64,2 -> vec128_load64 x
  | U32,8 -> vec256_load32 x
  | U64,4 -> vec256_load64 x
  | U128,2 -> vec256_load128 x

let vec_load2 #t x1 x0 =
  match t with
  | U64 -> vec128_load64s x1 x0
  | U128 -> vec256_load128s x1 x0

let vec_load4 #t x3 x2 x1 x0 =
  match t with
  | U32 -> vec128_load32s x3 x2 x1 x0
  | U64 -> vec256_load64s x3 x2 x1 x0

let vec_load8 #t x7 x6 x5 x4 x3 x2 x1 x0 =
  match t with
  | U32 -> vec256_load32s x7 x6 x5 x4 x3 x2 x1 x0

let vec_load16 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = admit()
let vec_load32 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15  = admit()


let vec_set (#t:v_inttype) (#w:width) (v:vec_t t w) (i:vec_index w) (x:uint_t t SEC) =
  match t,w with
  | U128,1 -> vec128_load128 x
  | _,1 -> x
  | U8,16 -> vec128_insert8 v x i
  | U32,4 -> vec128_insert32 v x i
  | U64,2 -> vec128_insert64 v x i
  | U8,32 -> vec256_insert8 v x i
  | U32,8 -> vec256_insert32 v x i
  | U64,4 -> vec256_insert64 v x i


let vec_add_mod (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | _,1 -> (x <: uint_t t SEC) +. y
  | U32,4 -> vec128_add32 x y
  | U64,2 -> vec128_add64 x y
  | U32,8 -> vec256_add32 x y
  | U64,4 -> vec256_add64 x y
  | U128,2 -> admit()

let vec_add_mod_lemma (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) = ()

let vec_sub_mod (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | _,1 -> (x <: uint_t t SEC) -. y
  | U32,4 -> vec128_sub32 x y
  | U64,2 -> vec128_sub64 x y
  | U32,8 -> vec256_sub32 x y
  | U64,4 -> vec256_sub64 x y
  | U128,2 -> admit()


let vec_mul_mod (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | _,1 -> (x <: uint_t t SEC) *. y
  | U32,4 -> vec128_mul32 x y
  | U64,2 -> vec128_mul64 x y
  | U32,8 -> vec256_mul32 x y
  | U64,4 -> vec256_mul64 x y
  | U128,2 -> admit()


let vec_smul_mod (#t:v_inttype) (#w:width) (x:vec_t t w) (y:uint_t t SEC) =
  match t,w with
  | _,1 -> (x <: uint_t t SEC) *. y
  | U32,4 -> vec128_smul32 x y
  | U64,2 -> vec128_smul64 x y
  | U32,8 -> vec256_smul32 x y
  | U64,4 -> vec256_smul64 x y
  | U128,2 -> admit()

let vec_xor (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | U128,1 -> vec128_xor x y
  | _,1 -> (x <: uint_t t SEC) ^. y
  | U8,16 -> vec128_xor x y
  | U32,4 -> vec128_xor x y
  | U64,2 -> vec128_xor x y
  | U8,32 -> vec256_xor x y
  | U32,8 -> vec256_xor x y
  | U64,4 -> vec256_xor x y
  | U128,2 -> admit()

let vec_xor_lemma (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) = ()

let vec_and (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | U128,1 -> vec128_and x y
  | _,1 -> (x <: uint_t t SEC) &. y
  | U8,16 -> vec128_and x y
  | U32,4 -> vec128_and x y
  | U64,2 -> vec128_and x y
  | U8,32 -> vec256_and x y
  | U32,8 -> vec256_and x y
  | U64,4 -> vec256_and x y
  | U128,2 -> admit()

let vec_and_lemma (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) = ()

let vec_or (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | U128,1 -> vec128_or x y
  | _,1 -> (x <: uint_t t SEC) |. y
  | U8,16 -> vec128_or x y
  | U32,4 -> vec128_or x y
  | U64,2 -> vec128_or x y
  | U8,32 -> vec256_or x y
  | U32,8 -> vec256_or x y
  | U64,4 -> vec256_or x y
  | U128,2 -> admit()

let vec_not (#t:v_inttype) (#w:width) (x:vec_t t w) =
  match t,w with
  | U128,1 -> vec128_lognot x
  | _,1 -> lognot (x <: uint_t t SEC)
  | U8,16 -> vec128_lognot x
  | U32,4 -> vec128_lognot x
  | U64,2 -> vec128_lognot x
  | U8,32 -> vec256_lognot x
  | U32,8 -> vec256_lognot x
  | U64,4 -> vec256_lognot x
  | U128,2 -> admit()

let vec_not_lemma (#t:v_inttype) (#w:width) (x:vec_t t w) = ()

let vec_shift_right (#t:v_inttype) (#w:width) (x:vec_t t w) (y:shiftval t) =
  match t,w with
  | U128,1 -> vec128_shift_right x y
  | _,1 -> (x <: uint_t t SEC) >>. y
  | U32,4 -> vec128_shift_right32 x y
  | U64,2 -> vec128_shift_right64 x y
  | U32,8 -> vec256_shift_right32 x y
  | U64,4 -> vec256_shift_right64 x y
  | U128,2 -> vec256_shift_right x y

let vec_shift_left (#t:v_inttype) (#w:width) (x:vec_t t w) (y:shiftval t) =
  match t,w with
  | U128,1 -> vec128_shift_left x y
  | _,1 -> (x <: uint_t t SEC) <<. y
  | U32,4 -> vec128_shift_left32 x y
  | U64,2 -> vec128_shift_left64 x y
  | U32,8 -> vec256_shift_left32 x y
  | U64,4 -> vec256_shift_left64 x y
  | U128,2 -> vec256_shift_left x y

let vec_rotate_right (#t:v_inttype) (#w:width) (x:vec_t t w) (y:rotval t) =
  match t,w with
  | U32,4 -> vec128_rotate_right32 x y
  | U32,8 -> vec256_rotate_right32 x y
  | _,_ ->  vec_or (vec_shift_left x (size (bits t) -. y)) (vec_shift_right x y)

let vec_rotate_left (#t:v_inttype) (#w:width) (x:vec_t t w) (y:rotval t) =
  match t,w with
  | U32,4 -> vec128_rotate_left32 x y
  | U32,8 -> vec256_rotate_left32 x y
  | _,_ ->  vec_or (vec_shift_left x y) (vec_shift_right x (size (bits t) -. y))


let vec_eq_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | U128,1 -> admit()
  | _,1 -> (eq_mask (x <: uint_t t SEC) y) <: vec_t t w
  | U32,4 -> vec128_eq32 x y
  | U64,2 -> vec128_eq64 x y
  | U32,8 -> vec256_eq32 x y
  | U64,4 -> vec256_eq64 x y
  | U128,2 -> admit()

let vec_neq_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  vec_not (vec_eq_mask #t #w x y)

let vec_lt_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | U128,1 -> admit()
  | _,1 -> lt_mask (x <: uint_t t SEC) y
  | U32,4 -> vec128_gt32 y x
  | U64,2 -> vec128_gt64 y x
  | U32,8 -> vec256_gt32 y x
  | U64,4 -> vec256_gt64 y x
  | U128,2 -> admit()

let vec_gt_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  vec_lt_mask #t #w y x

let vec_lte_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  vec_not (vec_gt_mask #t #w x y)

let vec_gte_mask (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  vec_not (vec_lt_mask #t #w x y)

let vec_interleave_low (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | _,1 -> x
  | U32,4 -> vec128_interleave_low32 x y
  | U64,2 -> vec128_interleave_low64 x y
  | U32,8 -> vec256_interleave_low32 x y
  | U64,4 -> vec256_interleave_low64 x y
  | U128,2 -> vec256_interleave_low128 x y

let vec_interleave_low_lemma2 #vt v1 v2 = admit()

let vec_interleave_low_lemma_uint64_4 v1 v2 = admit()

let vec_interleave_high (#t:v_inttype) (#w:width) (x:vec_t t w) (y:vec_t t w) =
  match t,w with
  | _,1 -> x
  | U32,4 -> vec128_interleave_high32 x y
  | U64,2 -> vec128_interleave_high64 x y
  | U32,8 -> vec256_interleave_high32 x y
  | U64,4 -> vec256_interleave_high64 x y
  | U128,2 -> vec256_interleave_high128 x y

let vec_interleave_high_lemma2 #vt v1 v2 = admit()

let vec_interleave_high_lemma_uint64_4 v1 v2 = admit()

let vec_permute2 #t v i1 i2 =
  match t with
  | U64 -> vec128_shuffle64 v i1 i2
  | U128 -> vec256_shuffle128 v i1 i2

let vec_permute4 #t v i1 i2 i3 i4 =
  match t with
  | U32 -> vec128_shuffle32 v i1 i2 i3 i4
  | U64 -> vec256_shuffle64 v i1 i2 i3 i4

let vec_permute8 #t v i1 i2 i3 i4 i5 i6 i7 i8 = admit()
let vec_permute16 #t = admit()
let vec_permute32 #t = admit()

let cast #t #w t' w' v = v

let cast_vec_u128_to_u64_lemma #w b = admit()
let cast_vec_u64_to_u128_lemma #w b = admit()

let vec_aes_enc key state =
  ni_aes_enc key state

let vec_aes_enc_lemma key state = admit()

let vec_aes_enc_last key state =
  ni_aes_enc_last key state

let vec_aes_enc_last_lemma key state = admit()

let vec_aes_keygen_assist key state =
  ni_aes_keygen_assist key state

let vec_aes_keygen_assist_lemma key state = admit()

let vec_clmul_lo_lo x y =
  ni_clmul x y (u8 0x00)

let vec_clmul_lo_hi x y =
  ni_clmul x y (u8 0x01)

let vec_clmul_hi_lo x y =
  ni_clmul x y (u8 0x10)

let vec_clmul_hi_hi x y =
  ni_clmul x y (u8 0x11)

let vec_from_bytes_le t w b = admit()
let vec_from_bytes_be t w b = admit()

let vec_load_le t w b =
  match t,w with
  | U128,1 -> vec128_load_le b
  | _,1 -> Lib.ByteBuffer.uint_from_bytes_le #t #SEC b
  | U32,4 -> vec128_load_le b
  | U64,2 -> vec128_load_le b
  | U32,8 -> vec256_load_le b
  | U64,4 -> vec256_load_le b
  | U128,2 -> vec256_load_le b

let vec_load_be t w b =
  match t,w with
  | U128,1 -> vec128_load_be b
  | _,1 -> Lib.ByteBuffer.uint_from_bytes_be #t #SEC b
  | U32,4 -> vec128_load32_be b
  | U64,2 -> vec128_load64_be b

let vec_to_bytes_le #vt #w v = admit()
let vec_to_bytes_be #vt #w v = admit()

let vec_store_le #t #w b v =
  match t,w with
  | U128,1 -> vec128_store_le b v
  | _,1 -> Lib.ByteBuffer.uint_to_bytes_le #t #SEC b v
  | U32,4 -> vec128_store_le b v
  | U64,2 -> vec128_store_le b v
  | U32,8 -> vec256_store_le b v
  | U64,4 -> vec256_store_le b v
  | U128,2 -> vec256_store_le b v

let vec_store_be #t #w b v =
  match t,w with
  | U128,1 -> vec128_store_be b v
  | _,1 -> Lib.ByteBuffer.uint_to_bytes_be #t #SEC b v
  | U32,4 -> vec128_store32_be b v
  | U64,2 -> vec128_store64_be b v
