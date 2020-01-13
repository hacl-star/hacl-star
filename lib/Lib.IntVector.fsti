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

inline_for_extraction noextract
val vec_v: #t:v_inttype -> #w:width -> vec_t t w -> vec_v_t t w

val vecv_extensionality: #t:v_inttype -> #w:width -> f1:vec_t t w -> f2:vec_t t w -> Lemma
  (requires vec_v f1 == vec_v f2)
  (ensures f1 == f2)

inline_for_extraction noextract
val vec_zero: t:v_inttype -> w:width -> v:vec_t t w{vec_v v == create w (mk_int 0)}

inline_for_extraction noextract
val vec_counter: t:v_inttype -> w:width -> v:vec_t t w{vec_v v == createi w mk_int}

inline_for_extraction noextract
val create2: #a:Type
  -> x0:a -> x1:a ->
  s:lseq a 2{
    s.[0] == x0 /\ s.[1] == x1}

inline_for_extraction noextract
val create4: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a ->
  s:lseq a 4{
    s.[0] == x0 /\ s.[1] == x1 /\
    s.[2] == x2 /\ s.[3] == x3}

inline_for_extraction noextract
val create8: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a ->
  s:lseq a 8{
    s.[0] == x0 /\ s.[1] == x1 /\
    s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\
    s.[6] == x6 /\ s.[7] == x7}

inline_for_extraction noextract
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

inline_for_extraction noextract
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

inline_for_extraction noextract
val vec_load: #t:v_inttype
  -> i:uint_t t SEC -> w:width ->
  v:vec_t t w{vec_v v == create w i}

inline_for_extraction noextract
val vec_load2: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC ->
  v:vec_t t 2{vec_v v == create2 i0 i1}

inline_for_extraction noextract
val vec_load4: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC ->
  v:vec_t t 4{vec_v v == create4 i0 i1 i2 i3}

inline_for_extraction noextract
val vec_load8: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC
  -> i4:uint_t t SEC -> i5:uint_t t SEC -> i6:uint_t t SEC -> i7:uint_t t SEC ->
  v:vec_t t 8{vec_v v == create8 i0 i1 i2 i3 i4 i5 i6 i7}

inline_for_extraction noextract
val vec_load16: #t:v_inttype
  -> i0:uint_t t SEC -> i1:uint_t t SEC -> i2:uint_t t SEC -> i3:uint_t t SEC
  -> i4:uint_t t SEC -> i5:uint_t t SEC -> i6:uint_t t SEC -> i7:uint_t t SEC
  -> i8:uint_t t SEC -> i9:uint_t t SEC -> i10:uint_t t SEC -> i11:uint_t t SEC
  -> i12:uint_t t SEC -> i13:uint_t t SEC -> i14:uint_t t SEC -> i15:uint_t t SEC ->
  v:vec_t t 16{vec_v v == create16 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15}

inline_for_extraction noextract
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

inline_for_extraction noextract
val vec_set: #t:v_inttype -> #w:width
  -> v:vec_t t w -> i:vec_index w -> x:uint_t t SEC ->
  v':vec_t t w{vec_v v' == upd (vec_v v) (size_v i) x}

inline_for_extraction noextract
val vec_get: #t:v_inttype -> #w:width
  -> v:vec_t t w -> i:vec_index w ->
  x:uint_t t SEC{x == index (vec_v v) (size_v i)}

inline_for_extraction noextract
val vec_add_mod: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w

noextract
val vec_add_mod_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_add_mod v1 v2) == map2 ( +. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v (vec_add_mod #t #w v1 v2))]

inline_for_extraction noextract
val vec_sub_mod: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( -. ) (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_mul_mod: #t:v_inttype{t <> U128} -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( *. ) (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_smul_mod: #t:v_inttype{t <> U128} -> #w:width -> v1:vec_t t w -> v2:uint_t t SEC -> v3:vec_t t w{vec_v v3 == map ( mul_mod v2 ) (vec_v v1)}

inline_for_extraction noextract
val vec_xor: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w

val vec_xor_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_xor v1 v2) == map2 ( ^. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v #t #w (vec_xor v1 v2))]

inline_for_extraction noextract
val vec_and: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w

val vec_and_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> Lemma
  (ensures (vec_v (vec_and v1 v2) == map2 ( &. ) (vec_v v1) (vec_v v2)))
  [SMTPat (vec_v #t #w (vec_and v1 v2))]

inline_for_extraction noextract
val vec_or: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 ( |. ) (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_not: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w

val vec_not_lemma: #t:v_inttype -> #w:width -> v1:vec_t t w -> Lemma
  (ensures (vec_v (vec_not v1) == map lognot (vec_v v1)))
  [SMTPat (vec_v #t #w (vec_not v1))]

inline_for_extraction noextract
let shift_right_i (#t:v_inttype) (s:shiftval t) (u:uint_t t SEC) : uint_t t SEC = shift_right u s

inline_for_extraction noextract
let shift_left_i (#t:v_inttype) (s:shiftval t) (u:uint_t t SEC) : uint_t t SEC = shift_left u s

inline_for_extraction noextract
let rotate_right_i (#t:v_inttype) (s:rotval t) (u:uint_t t SEC) : uint_t t SEC = rotate_right u s

inline_for_extraction noextract
let rotate_left_i (#t:v_inttype) (s:rotval t) (u:uint_t t SEC) : uint_t t SEC = rotate_left u s

inline_for_extraction noextract
val vec_shift_right: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (shift_right_i s) (vec_v v1)}

inline_for_extraction noextract
val vec_shift_left: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:shiftval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (shift_left_i s) (vec_v v1)}

inline_for_extraction noextract
val vec_rotate_right: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (rotate_right_i s) (vec_v v1)}

inline_for_extraction noextract
val vec_rotate_left: #t:v_inttype -> #w:width
  -> v1:vec_t t w -> s:rotval t{t <> U128 \/ uint_v s % 8 == 0} ->
  v2:vec_t t w{vec_v v2 == map (rotate_left_i s) (vec_v v1)}

inline_for_extraction noextract
val vec_eq_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 eq_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_neq_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 neq_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_lt_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 lt_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_gt_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 gt_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_lte_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 lte_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val vec_gte_mask: #t:v_inttype -> #w:width -> v1:vec_t t w -> v2:vec_t t w -> v3:vec_t t w{vec_v v3 == map2 gte_mask (vec_v v1) (vec_v v2)}

inline_for_extraction noextract
val cast: #t:v_inttype -> #w:width -> t':v_inttype -> w':width{bits t * w == bits t' * w'} -> vec_t t w -> vec_t t' w'

inline_for_extraction noextract
val vec_interleave_low: #t:v_inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

inline_for_extraction noextract
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

inline_for_extraction noextract
val vec_interleave_high: #t:v_inttype -> #w:width -> vec_t t w -> vec_t t w -> vec_t t w

inline_for_extraction noextract
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

inline_for_extraction noextract
val vec_permute2: #t:v_inttype -> v1:vec_t t 2
  -> i1:vec_index 2 -> i2:vec_index 2 ->
  v2:vec_t t 2{vec_v v2 == create2 (vec_v v1).[v i1] (vec_v v1).[v i2]}

inline_for_extraction noextract
val vec_permute4: #t:v_inttype -> v1:vec_t t 4
  -> i1:vec_index 4 -> i2:vec_index 4 -> i3:vec_index 4 -> i4:vec_index 4 ->
  v2:vec_t t 4{vec_v v2 == create4 (vec_v v1).[v i1] (vec_v v1).[v i2] (vec_v v1).[v i3] (vec_v v1).[v i4]}

inline_for_extraction noextract
val vec_permute8: #t:v_inttype -> v1:vec_t t 8
  -> i1:vec_index 8 -> i2:vec_index 8 -> i3:vec_index 8 -> i4:vec_index 8
  -> i5:vec_index 8 -> i6:vec_index 8 -> i7:vec_index 8 -> i8:vec_index 8 ->
  v2:vec_t t 8{vec_v v2 == create8 (vec_v v1).[v i1] (vec_v v1).[v i2] (vec_v v1).[v i3] (vec_v v1).[v i4]
                                   (vec_v v1).[v i5] (vec_v v1).[v i6] (vec_v v1).[v i7] (vec_v v1).[v i8]}

inline_for_extraction noextract
val vec_permute16: #t:v_inttype -> v1:vec_t t 16
  -> i1:vec_index 16 -> i2:vec_index 16 -> i3:vec_index 16 -> i4:vec_index 16
  -> i5:vec_index 16 -> i6:vec_index 16 -> i7:vec_index 16 -> i8:vec_index 16
  -> i9:vec_index 16  -> i10:vec_index 16 -> i11:vec_index 16 -> i12:vec_index 16
  -> i13:vec_index 16 -> i14:vec_index 16 -> i15:vec_index 16 -> i16:vec_index 16 ->
  v2:vec_t t 16{let vv1 = vec_v v1 in
    vec_v v2 == create16 vv1.[v i1] vv1.[v i2] vv1.[v i3] vv1.[v i4]
                         vv1.[v i5] vv1.[v i6] vv1.[v i7] vv1.[v i8]
                         vv1.[v i9] vv1.[v i10] vv1.[v i11] vv1.[v i12]
                         vv1.[v i13] vv1.[v i14] vv1.[v i15] vv1.[v i16]}

inline_for_extraction noextract
val vec_permute32: #t:v_inttype -> v1:vec_t t 32
  -> i1:vec_index 16 -> i2:vec_index 16 -> i3:vec_index 16 -> i4:vec_index 16
  -> i5:vec_index 16 -> i6:vec_index 16 -> i7:vec_index 16 -> i8:vec_index 16
  -> i9:vec_index 16 -> i10:vec_index 16 -> i11:vec_index 16 -> i12:vec_index 16
  -> i13:vec_index 16 -> i14:vec_index 16 -> i15:vec_index 16 -> i16:vec_index 16
  -> i17:vec_index 16 -> i18:vec_index 16 -> i19:vec_index 16 -> i20:vec_index 16
  -> i21:vec_index 16 -> i22:vec_index 16 -> i23:vec_index 16 -> i24:vec_index 16
  -> i25:vec_index 16 -> i26:vec_index 16 -> i27:vec_index 16 -> i28:vec_index 16
  -> i29:vec_index 16 -> i30:vec_index 16 -> i31:vec_index 16 -> i32:vec_index 16 ->
  v2:vec_t t 32{let vv1 = vec_v v1 in
    vec_v v2 == create32 vv1.[v i1] vv1.[v i2] vv1.[v i3] vv1.[v i4]
                         vv1.[v i5] vv1.[v i6] vv1.[v i7] vv1.[v i8]
                         vv1.[v i9] vv1.[v i10] vv1.[v i11] vv1.[v i12]
                         vv1.[v i13] vv1.[v i14] vv1.[v i15] vv1.[v i16]
                         vv1.[v i17] vv1.[v i18] vv1.[v i19] vv1.[v i20]
                         vv1.[v i21] vv1.[v i22] vv1.[v i23] vv1.[v i24]
                         vv1.[v i25] vv1.[v i26] vv1.[v i27] vv1.[v i28]
                         vv1.[v i29] vv1.[v i30] vv1.[v i31] vv1.[v i32]}

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

inline_for_extraction noextract
val vec_aes_enc: key:uint8x16 -> state:uint8x16 -> res:uint8x16

val vec_aes_enc_lemma: key:uint8x16 -> state:uint8x16 -> Lemma
  (ensures (vec_v (vec_aes_enc key state) == Spec.AES.aes_enc (vec_v key) (vec_v state)))
  [SMTPat (vec_v (vec_aes_enc key state))]

inline_for_extraction noextract
val vec_aes_enc_last: key:uint8x16 -> state:uint8x16 -> res:uint8x16

val vec_aes_enc_last_lemma: key:uint8x16 -> state:uint8x16 -> Lemma
  (ensures (vec_v (vec_aes_enc_last key state) == Spec.AES.aes_enc_last (vec_v key) (vec_v state)))
  [SMTPat (vec_v (vec_aes_enc_last key state))]

inline_for_extraction noextract
val vec_aes_keygen_assist: s:uint8x16 -> rcon:uint8 -> res:uint8x16

val vec_aes_keygen_assist_lemma: s:uint8x16 -> rcon:uint8 -> Lemma
  (ensures (vec_v (vec_aes_keygen_assist s rcon) == Spec.AES.aes_keygen_assist rcon (vec_v s)))
  [SMTPat (vec_v (vec_aes_keygen_assist s rcon))]

inline_for_extraction noextract
val vec_clmul_lo_lo: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction noextract
val vec_clmul_lo_hi: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction noextract
val vec_clmul_hi_lo: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction noextract
val vec_clmul_hi_hi: uint128x1 -> uint128x1 -> uint128x1

inline_for_extraction noextract
let ( +| ) #t #w = vec_add_mod #t #w
inline_for_extraction noextract
let ( -| ) #t #w = vec_sub_mod #t #w
inline_for_extraction noextract
let ( *| ) #t #w = vec_mul_mod #t #w
inline_for_extraction noextract
let ( ^| ) #t #w = vec_xor #t #w
inline_for_extraction noextract
let ( &| ) #t #w = vec_and #t #w
//inline_for_extraction noextract
//let ( || ) #t #w = vec_or #t #w
inline_for_extraction noextract
let ( ~| ) #t #w = vec_not #t #w
inline_for_extraction noextract
let ( >>| ) #t #w = vec_shift_right #t #w
inline_for_extraction noextract
let ( <<| ) #t #w = vec_shift_left #t #w
inline_for_extraction noextract
let ( >>>| ) #t #w = vec_rotate_right #t #w
inline_for_extraction noextract
let ( <<<| ) #t #w = vec_rotate_left #t #w

open Lib.ByteSequence
open Lib.Buffer
open FStar.HyperStack
open FStar.HyperStack.ST

inline_for_extraction noextract
val vec_from_bytes_le: vt:v_inttype -> w:width -> b:lseq uint8 ((numbytes vt) * w) -> v:vec_t vt w{vec_v v == uints_from_bytes_le b}

inline_for_extraction noextract
val vec_from_bytes_be: vt:v_inttype -> w:width -> b:lseq uint8 ((numbytes vt) * w) -> v:vec_t vt w{vec_v v == uints_from_bytes_be b}

inline_for_extraction noextract
val vec_load_le:
    vt:v_inttype
  -> w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w) ->
  Stack (vec_t vt w)
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ r == vec_from_bytes_le vt w (as_seq h0 b))

inline_for_extraction noextract
val vec_load_be:
    vt:v_inttype
  -> w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w) ->
  Stack (vec_t vt w)
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ r == vec_from_bytes_be vt w (as_seq h0 b))

inline_for_extraction noextract
val vec_to_bytes_le: #vt:v_inttype -> #w:width -> v:vec_t vt w -> b:lseq uint8 ((numbytes vt) * w){b == uints_to_bytes_le (vec_v v)}

inline_for_extraction noextract
val vec_to_bytes_be: #vt:v_inttype -> #w:width -> v:vec_t vt w -> b:lseq uint8 ((numbytes vt) * w){b == uints_to_bytes_be (vec_v v)}

inline_for_extraction noextract
val vec_store_le:
    #vt:v_inttype
  -> #w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w)
  -> v:vec_t vt w ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ as_seq h1 b == vec_to_bytes_le v)

inline_for_extraction noextract
val vec_store_be:
    #vt:v_inttype
  -> #w:width
  -> b:Lib.Buffer.lbuffer uint8 (size (numbytes vt) *! size w)
  -> v:vec_t vt w ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 -> h1 == h0 /\ as_seq h1 b == vec_to_bytes_be v)
