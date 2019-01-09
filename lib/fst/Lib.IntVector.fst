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
  assert(index s 0 == List.Tot.index l 0);
  assert(index s 1 == List.Tot.index l 1);
  assert(index s 2 == List.Tot.index l 2);
  assert(index s 3 == List.Tot.index l 3);
  s

let create8 #a x1 x2 x3 x4 x5 x6 x7 x8 = 
  [@inline_let]
  let l = [x1;x2;x3;x4;x5;x6;x7;x8] in
  assert_norm(List.Tot.length l == 8);
  [@inline_let]
  let s : lseq a 8 = of_list l in
  assert(index s 0 == List.Tot.index l 0);
  assert(index s 1 == List.Tot.index l 1);
  assert(index s 2 == List.Tot.index l 2);
  assert(index s 3 == List.Tot.index l 3);
  assert(index s 4 == List.Tot.index l 4);
  assert(index s 5 == List.Tot.index l 5);
  assert(index s 6 == List.Tot.index l 6);
  assert(index s 7 == List.Tot.index l 7);
  s

#set-options "--z3rlimit 100"
let create16 #a x1 x2 x3 x4 x5 x6 x7 x8  x9 x10 x11 x12 x13 x14 x15 x16 = 
  [@inline_let]
  let l = [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] in
  assert_norm(List.Tot.length l == 16);
  [@inline_let]
  let s : lseq a 16 = of_list l in
  assert(index s 0 == List.Tot.index l 0);
  assert(index s 1 == List.Tot.index l 1);
  assert(index s 2 == List.Tot.index l 2);
  assert(index s 3 == List.Tot.index l 3);
  assert(index s 4 == List.Tot.index l 4);
  assert(index s 5 == List.Tot.index l 5);
  assert(index s 6 == List.Tot.index l 6);
  assert(index s 7 == List.Tot.index l 7);
  assert(index s 8 == List.Tot.index l 8);
  assert(index s 9 == List.Tot.index l 9);
  assert(index s 10 == List.Tot.index l 10);
  assert(index s 11 == List.Tot.index l 11);
  assert(index s 12 == List.Tot.index l 12);
  assert(index s 13 == List.Tot.index l 13);
  assert(index s 14 == List.Tot.index l 14);
  assert(index s 15 == List.Tot.index l 15);
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

let create32 #a x1 x2 x3 x4 x5 x6 x7 x8  x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24  x25 x26 x27 x28 x29 x30 x31 x32 = 
 [@inline_let]
  let l = [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31;x32] in
  assert_norm(List.Tot.length l == 32);
  [@inline_let]
  let s : lseq a 32 = of_list l in
  assert(index s 0 == List.Tot.index l 0);
  assert(index s 1 == List.Tot.index l 1);
  assert(index s 2 == List.Tot.index l 2);
  assert(index s 3 == List.Tot.index l 3);
  assert(index s 4 == List.Tot.index l 4);
  assert(index s 5 == List.Tot.index l 5);
  assert(index s 6 == List.Tot.index l 6);
  assert(index s 7 == List.Tot.index l 7);
  assert(index s 8 == List.Tot.index l 8);
  assert(index s 9 == List.Tot.index l 9);
  assert(index s 10 == List.Tot.index l 10);
  assert(index s 11 == List.Tot.index l 11);
  assert(index s 12 == List.Tot.index l 12);
  assert(index s 13 == List.Tot.index l 13);
  assert(index s 14 == List.Tot.index l 14);
  assert(index s 15 == List.Tot.index l 15);
  assert(index s 16 == List.Tot.index l 16);
  assert(index s 17 == List.Tot.index l 17);
  assert(index s 18 == List.Tot.index l 18);
  assert(index s 19 == List.Tot.index l 19);
  assert(index s 20 == List.Tot.index l 20);
  assert(index s 21 == List.Tot.index l 21);
  assert(index s 22 == List.Tot.index l 22);
  assert(index s 23 == List.Tot.index l 23);
  assert(index s 24 == List.Tot.index l 24);
  assert(index s 25 == List.Tot.index l 25);
  assert(index s 26 == List.Tot.index l 26);
  assert(index s 27 == List.Tot.index l 27);
  assert(index s 28 == List.Tot.index l 28);
  assert(index s 29 == List.Tot.index l 29);
  assert(index s 30 == List.Tot.index l 30);
  assert(index s 31 == List.Tot.index l 31);
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

let vec_load16 #vt i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 = create16  i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 
let vec_load32 #vt i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 = create32  i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 

let vec_set #vt #w v i x = upd v (size_v i) x

let vec_add_mod #vt #w (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
map2 (Ints.add_mod #vt) v1 v2

let vec_add_mod_lemma #vt #w (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_sub_mod #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
map2 (Ints.sub_mod #vt) v1 v2

let vec_mul_mod #vt #w  (v1:vec_t vt w) (v2:vec_t vt w): vec_t vt w =
map2 (Ints.mul_mod #vt #SEC) v1 v2

let vec_smul_mod #vt #w  (v1:vec_t vt w) (v2:uint_t vt SEC): vec_t vt w =
map (Ints.mul_mod #vt #SEC v2) v1 

let vec_xor #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
map2 (Ints.logxor #vt) v1 v2

let vec_xor_lemma #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_and #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
map2 (Ints.logand #vt) v1 v2

let vec_and_lemma #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) = ()

let vec_or #vt #w  (v1:vec_t vt w) (v2:vec_t vt w) : vec_t vt w =
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

let vec_interleave_high #vt #w v1 v2 = 
  createi w (fun i -> if i % 2 = 0 then v1.[w/2 + i/2] else v2.[w/2 + i/2])

let vec_permute2 #vt v i1 i2 = 
  create2 v.[i1] v.[i2]

let vec_permute4 #vt v i1 i2 i3 i4 = 
  create4 v.[i1] v.[i2] v.[i3] v.[i4]

let vec_permute8 #vt v i1 i2 i3 i4 i5 i6 i7 i8 = create8 v.[i1] v.[i2] v.[i3] v.[i4] v.[i5] v.[i6] v.[i7] v.[i8]

let vec_permute16 #vt v i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 = create16  v.[i1] v.[i2] v.[i3] v.[i4] v.[i5] v.[i6] v.[i7] v.[i8] v.[i9] v.[i10] v.[i11] v.[i12] v.[i13] v.[i14] v.[i15] v.[i16]

let vec_permute32 #vt v i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 = create32  v.[i1] v.[i2] v.[i3] v.[i4] v.[i5] v.[i6] v.[i7] v.[i8] v.[i9] v.[i10] v.[i11] v.[i12] v.[i13] v.[i14] v.[i15] v.[i16] v.[i17] v.[i18] v.[i19] v.[i20] v.[i21] v.[i22] v.[i23] v.[i24] v.[i25] v.[i26] v.[i27] v.[i28] v.[i29] v.[i30] v.[i31] v.[i32]

let cast #t #w x = admit()
let vec_aes_enc x = admit()
let vec_aes_enc_lemma x = admit()
let vec_aes_enc_last x = admit()
let vec_aes_enc_last_lemma x = admit()
let vec_aes_keygen_assist x = admit()
let vec_aes_keygen_assist_lemma x = admit()
let vec_clmul_lo_lo x = admit()
let vec_clmul_lo_hi x = admit()
let vec_clmul_hi_lo x = admit()
let vec_clmul_hi_hi x = admit()
let vec_load_le vt w b = admit()
let vec_load_be vt w b = admit()
let vec_store_le #vt #w b v = admit()
let vec_store_be #vt #w b v = admit()
    
