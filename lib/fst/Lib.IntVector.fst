module Lib.IntVector

open FStar.Mul
open Lib.Sequence
module Ints = Lib.IntTypes

let vec_t t w = lseq (Ints.uint_t t SEC) w
let vec_v #t #w x = x

let vec_zero (t:v_inttype) (w:width) = create w (nat_to_uint 0)

let vec_counter (t:v_inttype) (w:width) = createi w nat_to_uint

let create2 #a x1 x2 =
  [@inline_let]
  let l = [x1;x2] in
  assert_norm(List.Tot.length l == 2);
  [@inline_let]
  let s : lseq a 2 = createL l in
  assert(s.[0] == List.Tot.index l 0);
  assert(s.[1] == List.Tot.index l 1);
  s

let create4 #a x1 x2 x3 x4 =
  [@inline_let]
  let l = [x1;x2;x3;x4] in
  assert_norm(List.Tot.length l == 4);
  [@inline_let]
  let s : lseq a 4 = of_list l in
  assert(s.[0] == List.Tot.index l 0);
  assert(s.[1] == List.Tot.index l 1);
  assert(s.[2] == List.Tot.index l 2);
  assert(s.[3] == List.Tot.index l 3);
  assert_norm(List.Tot.index l 0 == x1);
  assert_norm(List.Tot.index l 1 == x2);
  assert_norm(List.Tot.index l 2 == x3);
  assert_norm(List.Tot.index l 3 == x4);
  s

let create8 #a x1 x2 x3 x4 x5 x6 x7 x8 =
  [@inline_let]
  let l = [x1;x2;x3;x4;x5;x6;x7;x8] in
  assert_norm(List.Tot.length l == 8);
  [@inline_let]
  let s : lseq a 8 = of_list l in
  assert(s.[0] == List.Tot.index l 0);
  assert(s.[1] == List.Tot.index l 1);
  assert(s.[2] == List.Tot.index l 2);
  assert(s.[3] == List.Tot.index l 3);
  assert(s.[4] == List.Tot.index l 4);
  assert(s.[5] == List.Tot.index l 5);
  assert(s.[6] == List.Tot.index l 6);
  assert(s.[7] == List.Tot.index l 7);
  assert_norm(List.Tot.index l 0 == x1);
  assert_norm(List.Tot.index l 1 == x2);
  assert_norm(List.Tot.index l 2 == x3);
  assert_norm(List.Tot.index l 3 == x4);
  assert_norm(List.Tot.index l 4 == x5);
  assert_norm(List.Tot.index l 5 == x6);
  assert_norm(List.Tot.index l 6 == x7);
  assert_norm(List.Tot.index l 7 == x8);
  s

let create16 #a x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
  [@inline_let]
  let l = [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] in
  assert_norm(List.Tot.length l == 16);
  [@inline_let]
  let s : lseq a 16 = of_list l in
  assert(s.[0] == List.Tot.index l 0);
  assert(s.[1] == List.Tot.index l 1);
  assert(s.[2] == List.Tot.index l 2);
  assert(s.[3] == List.Tot.index l 3);
  assert(s.[4] == List.Tot.index l 4);
  assert(s.[5] == List.Tot.index l 5);
  assert(s.[6] == List.Tot.index l 6);
  assert(s.[7] == List.Tot.index l 7);
  assert(s.[8] == List.Tot.index l 8);
  assert(s.[9] == List.Tot.index l 9);
  assert(s.[10] == List.Tot.index l 10);
  assert(s.[11] == List.Tot.index l 11);
  assert(s.[12] == List.Tot.index l 12);
  assert(s.[13] == List.Tot.index l 13);
  assert(s.[14] == List.Tot.index l 14);
  assert(s.[15] == List.Tot.index l 15);
  assert_norm(List.Tot.index l 0 == x1);
  assert_norm(List.Tot.index l 1 == x2);
  assert_norm(List.Tot.index l 2 == x3);
  assert_norm(List.Tot.index l 3 == x4);
  assert_norm(List.Tot.index l 4 == x5);
  assert_norm(List.Tot.index l 5 == x6);
  assert_norm(List.Tot.index l 6 == x7);
  assert_norm(List.Tot.index l 7 == x8);
  assert_norm(List.Tot.index l 8 == x9);
  assert_norm(List.Tot.index l 9 == x10);
  assert_norm(List.Tot.index l 10 == x11);
  assert_norm(List.Tot.index l 11 == x12);
  assert_norm(List.Tot.index l 12 == x13);
  assert_norm(List.Tot.index l 13 == x14);
  assert_norm(List.Tot.index l 14 == x15);
  assert_norm(List.Tot.index l 15 == x16);
  s

let create32 #a x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 =
 [@inline_let]
  let l = [
    x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;
    x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31;x32] in
  assert_norm(List.Tot.length l == 32);
  [@inline_let]
  let s : lseq a 32 = of_list l in
  assert(s.[0] == List.Tot.index l 0);
  assert(s.[1] == List.Tot.index l 1);
  assert(s.[2] == List.Tot.index l 2);
  assert(s.[3] == List.Tot.index l 3);
  assert(s.[4] == List.Tot.index l 4);
  assert(s.[5] == List.Tot.index l 5);
  assert(s.[6] == List.Tot.index l 6);
  assert(s.[7] == List.Tot.index l 7);
  assert(s.[8] == List.Tot.index l 8);
  assert(s.[9] == List.Tot.index l 9);
  assert(s.[10] == List.Tot.index l 10);
  assert(s.[11] == List.Tot.index l 11);
  assert(s.[12] == List.Tot.index l 12);
  assert(s.[13] == List.Tot.index l 13);
  assert(s.[14] == List.Tot.index l 14);
  assert(s.[15] == List.Tot.index l 15);
  assert(s.[16] == List.Tot.index l 16);
  assert(s.[17] == List.Tot.index l 17);
  assert(s.[18] == List.Tot.index l 18);
  assert(s.[19] == List.Tot.index l 19);
  assert(s.[20] == List.Tot.index l 20);
  assert(s.[21] == List.Tot.index l 21);
  assert(s.[22] == List.Tot.index l 22);
  assert(s.[23] == List.Tot.index l 23);
  assert(s.[24] == List.Tot.index l 24);
  assert(s.[25] == List.Tot.index l 25);
  assert(s.[26] == List.Tot.index l 26);
  assert(s.[27] == List.Tot.index l 27);
  assert(s.[28] == List.Tot.index l 28);
  assert(s.[29] == List.Tot.index l 29);
  assert(s.[30] == List.Tot.index l 30);
  assert(s.[31] == List.Tot.index l 31);
  assert_norm(List.Tot.index l 0 == x1);
  assert_norm(List.Tot.index l 1 == x2);
  assert_norm(List.Tot.index l 2 == x3);
  assert_norm(List.Tot.index l 3 == x4);
  assert_norm(List.Tot.index l 4 == x5);
  assert_norm(List.Tot.index l 5 == x6);
  assert_norm(List.Tot.index l 6 == x7);
  assert_norm(List.Tot.index l 7 == x8);
  assert_norm(List.Tot.index l 8 == x9);
  assert_norm(List.Tot.index l 9 == x10);
  assert_norm(List.Tot.index l 10 == x11);
  assert_norm(List.Tot.index l 11 == x12);
  assert_norm(List.Tot.index l 12 == x13);
  assert_norm(List.Tot.index l 13 == x14);
  assert_norm(List.Tot.index l 14 == x15);
  assert_norm(List.Tot.index l 15 == x16);
  assert_norm(List.Tot.index l 16 == x17);
  assert_norm(List.Tot.index l 17 == x18);
  assert_norm(List.Tot.index l 18 == x19);
  assert_norm(List.Tot.index l 19 == x20);
  assert_norm(List.Tot.index l 20 == x21);
  assert_norm(List.Tot.index l 21 == x22);
  assert_norm(List.Tot.index l 22 == x23);
  assert_norm(List.Tot.index l 23 == x24);
  assert_norm(List.Tot.index l 24 == x25);
  assert_norm(List.Tot.index l 25 == x26);
  assert_norm(List.Tot.index l 26 == x27);
  assert_norm(List.Tot.index l 27 == x28);
  assert_norm(List.Tot.index l 28 == x29);
  assert_norm(List.Tot.index l 29 == x30);
  assert_norm(List.Tot.index l 30 == x31);
  assert_norm(List.Tot.index l 31 == x32);
  s

let vec_load #vt i len = create len i

let vec_load2 #vt i1 i2 = create2 i1 i2

let vec_load4 #vt i1 i2 i3 i4 = create4 i1 i2 i3 i4

let vec_load8 #vt i1 i2 i3 i4 i5 i6 i7 i8 = create8 i1 i2 i3 i4 i5 i6 i7 i8

let vec_load16 #vt i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 =
  create16 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16

let vec_load32 #vt i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 =
  create32 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32

let vec_set #vt #w v i x = upd v (size_v i) x

let vec_get #vt #w v i = index v (size_v i)

let vec_add_mod #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.add_mod #vt) v1 v2

let vec_add_mod_lemma #vt #w (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_sub_mod #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.sub_mod #vt) v1 v2

let vec_mul_mod #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.mul_mod #vt #SEC) v1 v2

let vec_smul_mod #vt #w (v1:vec_t vt w) (v2:uint_t vt SEC) : vec_t vt w =
  map (Ints.mul_mod #vt #SEC v2) v1

let vec_xor #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.logxor #vt) v1 v2

let vec_xor_lemma #vt #w (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_and #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.logand #vt) v1 v2

let vec_and_lemma #vt #w (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_or #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
  map2 (Ints.logor #vt) v1 v2

let vec_not #vt #w (v1:vec_t vt w) : vec_t vt w =
  map (Ints.lognot #vt) v1

let vec_not_lemma #vt #w (v1:vec_t vt w) = ()

let vec_shift_right #vt #w v1 s =
  map (shift_right_i s) v1

let vec_shift_left #vt #w v1 s =
  map (shift_left_i s) v1

let vec_rotate_right #vt #w v1 s =
  map (rotate_right_i s) v1

let vec_rotate_left #vt #w v1 s =
  map (rotate_left_i s) v1

let vec_eq_mask #vt #w v1 v2 =
  map2 Ints.eq_mask v1 v2

let vec_neq_mask #vt #w v1 v2 =
  map2 Ints.neq_mask v1 v2

let vec_lt_mask #vt #w v1 v2 =
  map2 Ints.lt_mask v1 v2

let vec_gt_mask #vt #w v1 v2 =
  map2 Ints.gt_mask v1 v2

let vec_lte_mask #vt #w v1 v2 =
  map2 Ints.lte_mask v1 v2

let vec_gte_mask #vt #w v1 v2 =
  map2 Ints.gte_mask v1 v2

let vec_interleave_low #vt #w v1 v2 =
  createi w (fun i -> if i % 2 = 0 then v1.[i/2] else v2.[i/2])

let vec_interleave_low_lemma2 #vt v1 v2 =
  let res = vec_interleave_low v1 v2 in
  assert (res.[0] == v1.[0]);
  assert (res.[1] == v2.[0]);
  eq_intro (vec_v res) (create2 (vec_v v1).[0] (vec_v v2).[0])

let vec_interleave_low_lemma_uint64_4 v1 v2 = admit()
//   let res = vec_interleave_low v1 v2 in
//   assert (res.[0] == v1.[0]);
//   assert (res.[1] == v2.[0]);
//   assert (res.[2] == v1.[1]);
//   assert (res.[3] == v2.[1]);
//   eq_intro (vec_v res) (create4 (vec_v v1).[0] (vec_v v2).[0] (vec_v v1).[2] (vec_v v2).[2])

let vec_interleave_high #vt #w v1 v2 =
  createi w (fun i -> if i % 2 = 0 then v1.[w/2 + i/2] else v2.[w/2 + i/2])

let vec_interleave_high_lemma2 #vt v1 v2 =
  let res = vec_interleave_high v1 v2 in
  assert (res.[0] == v1.[1]);
  assert (res.[1] == v2.[1]);
  eq_intro (vec_v res) (create2 (vec_v v1).[1] (vec_v v2).[1])

let vec_interleave_high_lemma_uint64_4 v1 v2 = admit()
//   let res = vec_interleave_high v1 v2 in
//   assert (res.[0] == v1.[2]);
//   assert (res.[1] == v2.[2]);
//   assert (res.[2] == v1.[3]);
//   assert (res.[3] == v2.[3]);
//   eq_intro (vec_v res) (create4 (vec_v v1).[1] (vec_v v2).[1] (vec_v v1).[3] (vec_v v2).[3])

let vec_permute2 #vt v i1 i2 =
  create2 v.[size_v i1] v.[size_v i2]

let vec_permute4 #vt v i1 i2 i3 i4 =
  create4 v.[size_v i1] v.[size_v i2] v.[size_v i3] v.[size_v i4]

let vec_permute8 #vt v i1 i2 i3 i4 i5 i6 i7 i8 =
  create8 v.[size_v i1] v.[size_v i2] v.[size_v i3] v.[size_v i4]
          v.[size_v i5] v.[size_v i6] v.[size_v i7] v.[size_v i8]

let vec_permute16 #vt v i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 =
  create16 v.[size_v i1] v.[size_v i2] v.[size_v i3] v.[size_v i4]
           v.[size_v i5] v.[size_v i6] v.[size_v i7] v.[size_v i8]
           v.[size_v i9] v.[size_v i10] v.[size_v i11] v.[size_v i12]
           v.[size_v i13] v.[size_v i14] v.[size_v i15] v.[size_v i16]

let vec_permute32 #vt v i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 =
  create32 v.[size_v i1] v.[size_v i2] v.[size_v i3] v.[size_v i4]
           v.[size_v i5] v.[size_v i6] v.[size_v i7] v.[size_v i8]
           v.[size_v i9] v.[size_v i10] v.[size_v i11] v.[size_v i12]
           v.[size_v i13] v.[size_v i14] v.[size_v i15] v.[size_v i16]
           v.[size_v i17] v.[size_v i18] v.[size_v i19] v.[size_v i20]
           v.[size_v i21] v.[size_v i22] v.[size_v i23] v.[size_v i24]
           v.[size_v i25] v.[size_v i26] v.[size_v i27] v.[size_v i28]
           v.[size_v i29] v.[size_v i30] v.[size_v i31] v.[size_v i32]

let cast #t #w t' w' x = admit()

let cast_vec_u128_to_u64_lemma #w b = admit()
let cast_vec_u64_to_u128_lemma #w b = admit()

let vec_aes_enc key state = admit()
let vec_aes_enc_lemma key state = admit()
let vec_aes_enc_last key state = admit()
let vec_aes_enc_last_lemma key state = admit()
let vec_aes_keygen_assist key state = admit()
let vec_aes_keygen_assist_lemma key state = admit()

let vec_clmul_lo_lo x y = admit()
let vec_clmul_lo_hi x y = admit()
let vec_clmul_hi_lo x y = admit()
let vec_clmul_hi_hi x y = admit()

let vec_from_bytes_le vt w b = uints_from_bytes_le #vt #SEC #w b
let vec_from_bytes_be vt w b = uints_from_bytes_be #vt #SEC #w b

let vec_load_le vt w b = admit()
let vec_load_be vt w b = admit()

let vec_to_bytes_le #vt #w v = uints_to_bytes_le #vt #SEC #w v
let vec_to_bytes_be #vt #w v = uints_to_bytes_be #vt #SEC #w v

let vec_store_le #vt #w b v = admit()
let vec_store_be #vt #w b v = admit()
