module Lib.IntVector

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes

let v_inttype = t:inttype{unsigned t /\ ~(U1? t)}

let width = n:size_nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8 \/ n == 16 \/ n == 32}
let vec_index (w:width) = n:size_t{v n < w}
let vec_v_t (t:v_inttype{unsigned t}) (w:width) = lseq (uint_t t SEC) w

inline_for_extraction
val vec_t: t:v_inttype -> w:width -> Type0

inline_for_extraction 
val vec_v: #t:v_inttype -> #w:width -> vec_t t w -> vec_v_t t w

val vecv_extensionality: #t:v_inttype -> #w:width -> f1:vec_t t w -> f2:vec_t t w -> Lemma
  (requires vec_v f1 == vec_v f2)
  (ensures f1 == f2)

inline_for_extraction 
val vec_zero: t:v_inttype -> w:width -> v:vec_t t w{vec_v v == create w (mk_int 0)}

inline_for_extraction 
val vec_counter: t:v_inttype -> w:width -> v:vec_t t w{vec_v v == createi w mk_int}

inline_for_extraction 
val create2: #a:Type
  -> x0:a -> x1:a ->
  s:lseq a 2{
    s.[0] == x0 /\ s.[1] == x1}

inline_for_extraction 
val create4: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a ->
  s:lseq a 4{
    s.[0] == x0 /\ s.[1] == x1 /\
    s.[2] == x2 /\ s.[3] == x3}

inline_for_extraction 
val create8: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a ->
  s:lseq a 8{
    s.[0] == x0 /\ s.[1] == x1 /\
    s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\
    s.[6] == x6 /\ s.[7] == x7}

inline_for_extraction 
val create16: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a ->
  s:lseq a 16{
    s.[0] == x0 /\ s.[1] == x1 /\
    s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\
    s.[6] == x6 /\ s.[7] == x7 /\
    s.[8] == x8 /\ s.[9] == x9 /\
    s.[10] == x10 /\ s.[11] == x11 /\
    s.[12] == x12 /\ s.[13] == x13 /\
    s.[14] == x14 /\ s.[15] == x15}

inline_for_extraction 
val create32: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a
  -> x16:a -> x17:a -> x18:a -> x19:a -> x20:a -> x21:a -> x22:a -> x23:a
  -> x24:a -> x25:a -> x26:a -> x27:a -> x28:a -> x29:a -> x30:a -> x31:a ->
  s:lseq a 32{
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\ s.[6] == x6 /\ s.[7] == x7 /\
    s.[8] == x8 /\ s.[9] == x9 /\ s.[10] == x10 /\ s.[11] == x11 /\
    s.[12] == x12 /\ s.[13] == x13 /\ s.[14] == x14 /\ s.[15] == x15 /\
    s.[16] == x16 /\ s.[17] == x17 /\ s.[18] == x18 /\ s.[19] == x19 /\
    s.[20] == x20 /\ s.[21] == x21 /\ s.[22] == x22 /\ s.[23] == x23 /\
    s.[24] == x24 /\ s.[25] == x25 /\ s.[26] == x26 /\ s.[27] == x27 /\
    s.[28] == x28 /\ s.[29] == x29 /\ s.[30] == x30 /\ s.[31] == x31}

inline_for_extraction 
val vec_load: #t:v_inttype
  -> i:uint_t t SEC -> w:width ->
  v:vec_t t w{vec_v v == create w i}

inline_for_extraction 
val vec_load2: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC ->
  v:vec_t t 2{vec_v v == create2 i0 i1}

inline_for_extraction 
val vec_load4: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC ->
  v:vec_t t 4{vec_v v == create4 i0 i1 i2 i3}

inline_for_extraction 
val vec_load8: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC
  -> i4:uint_t t SEC -> i5:uint_t t SEC -> i6:uint_t t SEC -> i7:uint_t t SEC ->
  v:vec_t t 8{vec_v v == create8 i0 i1 i2 i3 i4 i5 i6 i7}

inline_for_extraction 
val vec_load16: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC
  -> i4:uint_t t SEC -> i5:uint_t t SEC -> i6:uint_t t SEC -> i7:uint_t t SEC
  -> i8:uint_t t SEC -> i9:uint_t t SEC -> i10:uint_t t SEC -> i11:uint_t t SEC
  -> i12:uint_t t SEC -> i13:uint_t t SEC -> i14:uint_t t SEC -> i15:uint_t t SEC ->
  v:vec_t t 16{vec_v v == create16 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15}

inline_for_extraction 
val vec_load32: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC
  -> i4:uint_t t SEC -> i5:uint_t t SEC -> i6:uint_t t SEC -> i7:uint_t t SEC
  -> i8:uint_t t SEC -> i9:uint_t t SEC -> i10:uint_t t SEC -> i11:uint_t t SEC
  -> i12:uint_t t SEC -> i13:uint_t t SEC -> i14:uint_t t SEC -> i15:uint_t t SEC
  -> i16:uint_t t SEC -> i17:uint_t t SEC -> i18:uint_t t SEC -> i19:uint_t t SEC
  -> i20:uint_t t SEC -> i21:uint_t t SEC -> i22:uint_t t SEC -> i23:uint_t t SEC
  -> i24:uint_t t SEC -> i25:uint_t t SEC -> i26:uint_t t SEC -> i27:uint_t t SEC
  -> i28:uint_t t SEC -> i29:uint_t t SEC -> i30:uint_t t SEC -> i31:uint_t t SEC ->
  v:vec_t t 32{vec_v v == create32 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                                   i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31}

inline_for_extraction 
val vec_set: #t:v_inttype -> #w:width
  -> v:vec_t t w -> i:vec_index w -> x:uint_t t SEC ->
  v':vec_t t w{vec_v v' == upd (vec_v v) (size_v i) x}

inline_for_extraction 
val vec_get: #t:v_inttype -> #w:width
  -> v:vec_t t w -> i:vec_index w ->
  x:uint_t t SEC{x == index (vec_v v) (size_v i)}

inline_for_extraction 
val vec_add_mod: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> vec_t t w


val vec_add_mod_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_add_mod v1 v2) == map2 ( +. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v (vec_add_mod #t #w v1 v2))]

inline_for_extraction 
val vec_sub_mod: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( -. ) (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_mul_mod: #t:v_inttype{t <> U128} -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( *. ) (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_smul_mod: #t:v_inttype{t <> U128} -> #w:width -> v1:vec_t t w -> v2:uint_t t SEC -> v3:vec_t t w{vec_v v3 == map ( mul_mod v2 ) (vec_v v1)}

inline_for_extraction 
val vec_xor: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> vec_t t w

val vec_xor_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_xor v1 v2) == map2 ( ^. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v #t #w (vec_xor v1 v2))]

inline_for_extraction 
val vec_and: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> vec_t t w

val vec_and_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_and v1 v2) == map2 ( &. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v #t #w (vec_and v1 v2))]

inline_for_extraction 
val vec_or: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( |. ) (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_not: #t:v_inttype -> #w:width -> v1:vec_t t w -> vec_t t w

val vec_not_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> Lemma
  (ensures (vec_v (vec_not v1) == map lognot (vec_v v1)))
  [SMTPat (vec_v #t #w (vec_not v1))]

inline_for_extraction 
val vec_shift_right: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (shift_right_i s) (vec_v v1)}

inline_for_extraction 
val vec_shift_left: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (shift_left_i s) (vec_v v1)}

inline_for_extraction 
val vec_rotate_right: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} -> vec_t t w

val vec_rotate_right_lemma: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} ->
  Lemma (ensures (vec_v (vec_rotate_right v1 s) == map (rotate_right_i s) (vec_v v1)))
	[SMTPat (vec_v (vec_rotate_right #t #w v1 s))]

inline_for_extraction 
val vec_rotate_left: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (rotate_left_i s) (vec_v v1)}

inline_for_extraction 
val vec_eq_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 eq_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_neq_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 neq_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_lt_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 lt_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_gt_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 gt_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_lte_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 lte_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val vec_gte_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 gte_mask (vec_v v1) (vec_v v2)}

inline_for_extraction 
val cast: #t:v_inttype -> #w:width -> t':v_inttype -> w':width{bits t * w == bits t' * w'} -> vec_t t w -> vec_t t' w'

inline_for_extraction 
val vec_interleave_low: #t:v_inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

inline_for_extraction 
val vec_interleave_low_n: #t:v_inttype -> #w:width -> n:width{w % n == 0} -> vec_t t w -> vec_t t w -> vec_t t w

val vec_interleave_low_lemma2: #t:v_inttype -> v1:vec_t t 2 -> v2:vec_t t 2 -> Lemma
  (ensures (vec_v (vec_interleave_low v1 v2) == create2 (vec_v v1).[0] (vec_v v2).[0]))

val vec_interleave_low_lemma_uint32_4: v1:vec_t U32 4 -> v2:vec_t U32 4 -> Lemma
  (ensures (vec_v (vec_interleave_low v1 v2) == create4 (vec_v v1).[0] (vec_v v2).[0] (vec_v v1).[1] (vec_v v2).[1]))

val vec_interleave_low_lemma_uint32_8: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_low v1 v2) ==
    create8 (vec_v v1).[0] (vec_v v2).[0] (vec_v v1).[1] (vec_v v2).[1] (vec_v v1).[4] (vec_v v2).[4] (vec_v v1).[5] (vec_v v2).[5]))

val vec_interleave_low_lemma_uint64_4: v1:vec_t U64 4 -> v2:vec_t U64 4 -> Lemma
  (ensures (vec_v (vec_interleave_low v1 v2) == create4 (vec_v v1).[0] (vec_v v2).[0] (vec_v v1).[2] (vec_v v2).[2]))

val vec_interleave_low_n_lemma_uint32_4_2: v1:vec_t U32 4 -> v2:vec_t U32 4 -> Lemma
  (ensures (vec_v (vec_interleave_low_n 2 v1 v2) == create4 (vec_v v1).[0] (vec_v v1).[1] (vec_v v2).[0] (vec_v v2).[1]))

val vec_interleave_low_n_lemma_uint32_8_2: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_low_n 2 v1 v2) ==
    create8 (vec_v v1).[0] (vec_v v1).[1] (vec_v v1).[2] (vec_v v1).[3] (vec_v v2).[0] (vec_v v2).[1] (vec_v v2).[2] (vec_v v2).[3]))

val vec_interleave_low_n_lemma_uint32_8_4: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_low_n 4 v1 v2) ==
    create8 (vec_v v1).[0] (vec_v v1).[1] (vec_v v2).[0] (vec_v v2).[1] (vec_v v1).[4] (vec_v v1).[5] (vec_v v2).[4] (vec_v v2).[5]))

val vec_interleave_low_n_lemma_uint64_4_2: v1:vec_t U64 4 -> v2:vec_t U64 4 -> Lemma
  (ensures (vec_v (vec_interleave_low_n 2 v1 v2) == create4 (vec_v v1).[0] (vec_v v1).[1] (vec_v v2).[0] (vec_v v2).[1]))

inline_for_extraction 
val vec_interleave_high: #t:v_inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

inline_for_extraction 
val vec_interleave_high_n: #t:v_inttype -> #w:width -> n:width{w % n == 0} -> vec_t t w -> vec_t t w -> vec_t t w

val vec_interleave_high_lemma2: #t:v_inttype -> v1:vec_t t 2 -> v2:vec_t t 2 -> Lemma
  (ensures (vec_v (vec_interleave_high v1 v2) == create2 (vec_v v1).[1] (vec_v v2).[1]))

val vec_interleave_high_lemma_uint32_4: v1:vec_t U32 4 -> v2:vec_t U32 4 -> Lemma
  (ensures (vec_v (vec_interleave_high v1 v2) == create4 (vec_v v1).[2] (vec_v v2).[2] (vec_v v1).[3] (vec_v v2).[3]))

val vec_interleave_high_lemma_uint32_8: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_high v1 v2) ==
    create8 (vec_v v1).[2] (vec_v v2).[2] (vec_v v1).[3] (vec_v v2).[3] (vec_v v1).[6] (vec_v v2).[6] (vec_v v1).[7] (vec_v v2).[7]))

val vec_interleave_high_lemma_uint64_4: v1:vec_t U64 4 -> v2:vec_t U64 4 -> Lemma
  (ensures (vec_v (vec_interleave_high v1 v2) == create4 (vec_v v1).[1] (vec_v v2).[1] (vec_v v1).[3] (vec_v v2).[3]))

val vec_interleave_high_n_lemma_uint32_4_2: v1:vec_t U32 4 -> v2:vec_t U32 4 -> Lemma
  (ensures (vec_v (vec_interleave_high_n 2 v1 v2) == create4 (vec_v v1).[2] (vec_v v1).[3] (vec_v v2).[2] (vec_v v2).[3]))

val vec_interleave_high_n_lemma_uint32_8_2: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_high_n 2 v1 v2) ==
    create8 (vec_v v1).[4] (vec_v v1).[5] (vec_v v1).[6] (vec_v v1).[7] (vec_v v2).[4] (vec_v v2).[5] (vec_v v2).[6] (vec_v v2).[7]))

val vec_interleave_high_n_lemma_uint32_8_4: v1:vec_t U32 8 -> v2:vec_t U32 8 -> Lemma
  (ensures (vec_v (vec_interleave_high_n 4 v1 v2) ==
    create8 (vec_v v1).[2] (vec_v v1).[3] (vec_v v2).[2] (vec_v v2).[3] (vec_v v1).[6] (vec_v v1).[7] (vec_v v2).[6] (vec_v v2).[7]))

val vec_interleave_high_n_lemma_uint64_4_2: v1:vec_t U64 4 -> v2:vec_t U64 4 -> Lemma
  (ensures (vec_v (vec_interleave_high_n 2 v1 v2) == create4 (vec_v v1).[2] (vec_v v1).[3] (vec_v v2).[2] (vec_v v2).[3]))

val vec_shift_right_uint128_small2: v1:vec_t U64 4 -> s:shiftval U128{uint_v s % 8 == 0 /\ 0 < uint_v s /\ uint_v s < 64} -> Lemma
  (let v2 = cast U64 4 (vec_shift_right (cast U128 2 v1) s) in
   vec_v v2 == create4
     (((vec_v v1).[0] >>. s) |. ((vec_v v1).[1] <<. (64ul -! s)))
      ((vec_v v1).[1] >>. s)
     (((vec_v v1).[2] >>. s) |. ((vec_v v1).[3] <<. (64ul -! s)))
      ((vec_v v1).[3] >>. s))

inline_for_extraction 
val vec_rotate_right_lanes: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:size_t{v s <= w} -> vec_t t w

val vec_rotate_right_lanes2_lemma: #t:v_inttype -> v1:vec_t t 2 -> s:size_t{v s <= 2} ->
  Lemma (ensures (vec_v (vec_rotate_right_lanes v1 s) ==
                  create2 (vec_v v1).[(v s)% 2] (vec_v v1).[(v s + 1)%2]))
	[SMTPat (vec_v (vec_rotate_right_lanes #t v1 s))]

val vec_rotate_right_lanes4_lemma: #t:v_inttype -> v1:vec_t t 4 -> s:size_t{v s <= 4} ->
  Lemma (ensures (vec_v (vec_rotate_right_lanes v1 s) ==
                  create4 (vec_v v1).[(v s) % 4] (vec_v v1).[(v s + 1) % 4] (vec_v v1).[(v s + 2) % 4] (vec_v v1).[(v s + 3) % 4]))
	[SMTPat (vec_v (vec_rotate_right_lanes #t v1 s))]


inline_for_extraction 
val vec_rotate_left_lanes: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:size_t{v s <= w} -> vec_t t w

val vec_rotate_left_lanes2_lemma: #t:v_inttype -> v1:vec_t t 2 -> s:size_t{v s <= 2} ->
  Lemma (ensures (vec_v (vec_rotate_left_lanes v1 s) ==
                  vec_v (vec_rotate_right_lanes v1 (2ul -. s))))
	[SMTPat (vec_v (vec_rotate_left_lanes #t v1 s))]

val vec_rotate_left_lanes4_lemma: #t:v_inttype -> v1:vec_t t 4 -> s:size_t{v s <= 4} ->
  Lemma (ensures (vec_v (vec_rotate_left_lanes v1 s) ==
                  vec_v (vec_rotate_right_lanes v1 (4ul -. s))))
	[SMTPat (vec_v (vec_rotate_left_lanes #t v1 s))]


type uint128x1 = vec_t U128 1
type uint128x2 = vec_t U128 2
type uint64x2 = vec_t U64 2
type uint64x4 = vec_t U64 4
type uint32x4 = vec_t U32 4
type uint32x8 = vec_t U32 8
type uint16x8 = vec_t U16 8
type uint16x16 = vec_t U16 16
type uint8x16 = vec_t U8 16
type uint8x32 = vec_t U8 32

inline_for_extraction 
val vec_aes_enc: key:uint8x16 -> state:uint8x16 -> uint8x16

val vec_aes_enc_lemma: key:uint8x16 -> state:uint8x16 -> Lemma
  (ensures (vec_v (vec_aes_enc key state) == Spec.AES.aes_enc (vec_v key) (vec_v state)))
  [SMTPat (vec_v (vec_aes_enc key state))]

inline_for_extraction 
val vec_aes_enc_last: key:uint8x16 -> state:uint8x16 -> uint8x16

val vec_aes_enc_last_lemma: key:uint8x16 -> state:uint8x16 -> Lemma
  (ensures (vec_v (vec_aes_enc_last key state) == Spec.AES.aes_enc_last (vec_v key) (vec_v state)))
  [SMTPat (vec_v (vec_aes_enc_last key state))]

inline_for_extraction 
val vec_aes_keygen_assist: s:uint8x16 -> rcon:uint8 -> uint8x16

val vec_aes_keygen_assist_lemma: s:uint8x16 -> rcon:uint8 -> Lemma
  (ensures (vec_v (vec_aes_keygen_assist s rcon) == Spec.AES.aes_keygen_assist rcon (vec_v s)))
  [SMTPat (vec_v (vec_aes_keygen_assist s rcon))]

inline_for_extraction 
val vec_clmul_lo_lo: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction 
val vec_clmul_lo_hi: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction 
val vec_clmul_hi_lo: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction 
val vec_clmul_hi_hi: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction 
let ( +| ) #t #w = vec_add_mod #t #w
inline_for_extraction 
let ( -| ) #t #w = vec_sub_mod #t #w
inline_for_extraction 
let ( *| ) #t #w = vec_mul_mod #t #w
inline_for_extraction 
let ( ^| ) #t #w = vec_xor #t #w
inline_for_extraction 
let ( &| ) #t #w = vec_and #t #w
//inline_for_extraction 
//let ( || ) #t #w = vec_or #t #w
inline_for_extraction 
let ( ~| ) #t #w = vec_not #t #w
inline_for_extraction 
let ( >>| ) #t #w = vec_shift_right #t #w
inline_for_extraction 
let ( <<| ) #t #w = vec_shift_left #t #w
inline_for_extraction 
let ( >>>| ) #t #w = vec_rotate_right #t #w
inline_for_extraction 
let ( <<<| ) #t #w = vec_rotate_left #t #w

open Lib.ByteSequence
open Lib.Buffer
open FStar.HyperStack
open FStar.HyperStack.ST

inline_for_extraction 
val vec_from_bytes_le: vt:v_inttype -> w:width -> b:lseq uint8 ((numbytes vt) * w) -> v:vec_t vt w{vec_v v == uints_from_bytes_le b}

inline_for_extraction 
val vec_from_bytes_be: vt:v_inttype -> w:width -> b:lseq uint8 ((numbytes vt) * w) -> v:vec_t vt w{vec_v v == uints_from_bytes_be b}

inline_for_extraction 
val vec_load_le:
    vt:v_inttype
  -> w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w) ->
  Stack (vec_t vt w)
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ r == vec_from_bytes_le vt w (as_seq h0 b))

inline_for_extraction 
val vec_load_be:
    vt:v_inttype
  -> w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w) ->
  Stack (vec_t vt w)
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ r == vec_from_bytes_be vt w (as_seq h0 b))

inline_for_extraction 
val vec_to_bytes_le: #vt:v_inttype -> #w:width -> v:vec_t vt w -> b:lseq uint8 ((numbytes vt) * w){b == uints_to_bytes_le (vec_v v)}

inline_for_extraction 
val vec_to_bytes_be: #vt:v_inttype -> #w:width -> v:vec_t vt w -> b:lseq uint8 ((numbytes vt) * w){b == uints_to_bytes_be (vec_v v)}

inline_for_extraction 
val vec_store_le:
    #vt:v_inttype
  -> #w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w)
  -> v:vec_t vt w ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ as_seq h1 b == vec_to_bytes_le v)

inline_for_extraction 
val vec_store_be:
    #vt:v_inttype
  -> #w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w)
  -> v:vec_t vt w ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ as_seq h1 b == vec_to_bytes_be v)
