module Lib.IntVector

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes

let width = n:size_nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8 \/ n == 16 \/ n == 32}
val vec_t: t:inttype -> w:width -> Type0
type vec_index (w:width) = n:size_nat{n < w}

val vec_load: #t:inttype -> uint_t t SEC -> w:width -> vec_t t w
val vec_load1: #t:inttype -> uint_t t SEC -> vec_t t 1
val vec_load2: #t:inttype -> uint_t t SEC -> uint_t t SEC -> vec_t t 2
val vec_load4: #t:inttype -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> vec_t t 4
val vec_load8: #t:inttype -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> vec_t t 8
val vec_load16: #t:inttype -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> vec_t t 16
val vec_load32: #t:inttype -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC -> uint_t t SEC  -> uint_t t SEC -> uint_t t SEC -> vec_t t 32


val vec_add_mod: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_sub_mod: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_mul_mod: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_xor: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_and: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_or: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_not: #t:inttype -> #w:width -> vec_t t w -> vec_t t w
val vec_shift_right: #t:inttype -> #w:width -> vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} -> vec_t t w
val vec_shift_left: #t:inttype -> #w:width -> vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} -> vec_t t w
val vec_rotate_right: #t:inttype -> #w:width -> vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} -> vec_t t w
val vec_rotate_left: #t:inttype -> #w:width -> vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} -> vec_t t w
val vec_eq_mask: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_lt_mask: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_gt_mask: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_lte_mask: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_gte_mask: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

val vec_interleave_low: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w
val vec_interleave_high: #t:inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

val vec_permute2: #t:inttype -> vec_t t 2 -> vec_index 2 -> vec_index 2 -> vec_t t 2
val vec_permute4: #t:inttype -> vec_t t 4 -> vec_index 4 -> vec_index 4 -> vec_index 4 -> vec_index 4 -> vec_t t 4
val vec_permute8: #t:inttype -> vec_t t 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_index 8 -> vec_t t 8
val vec_permute16: #t:inttype -> vec_t t 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_index 16 -> vec_t t 16
val vec_permute32: #t:inttype -> vec_t t 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_index 32 -> vec_t t 32

val cast: #t:inttype -> #w:width -> t':inttype -> w':width{bits t * w == bits t' * w'} -> vec_t t w -> vec_t t' w'

type uint128x1 = vec_t U128 1
type uint128x2 = vec_t U128 2
type uint64x2 = vec_t U64 2
type uint64x4 = vec_t U64 2
type uint32x4 = vec_t U32 4
type uint32x8 = vec_t U32
type uint16x8 = vec_t U16 8
type uint16x16 = vec_t U16 1
type uint8x16 = vec_t U8 16
type uint8x32 = vec_t U8 32

val vec_aes_enc: uint128x1 -> uint128x1 -> uint128x1
val vec_aes_enc_last: uint128x1 -> uint128x1 -> uint128x1
val vec_aes_keygen_assist: uint128x1 -> byte_t -> uint128x1
val vec_clmul: uint128x1 -> uint128x1 -> uint128x1

let ( +| ) #t #w = vec_add_mod #t #w
let ( -| ) #t #w = vec_add_mod #t #w
let ( ^| ) #t #w = vec_xor #t #w
let ( &| ) #t #w = vec_and #t #w
let ( || ) #t #w = vec_or #t #w
let ( ~| ) #t #w = vec_not #t #w
let ( >>| ) #t #w = vec_shift_right #t #w
let ( <<| ) #t #w = vec_shift_left #t #w
let ( >>>| ) #t #w = vec_rotate_right #t #w
let ( <<<| ) #t #w = vec_rotate_left #t #w
