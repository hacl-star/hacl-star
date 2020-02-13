module Hacl.Spec.Chacha20.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector

open Hacl.Spec.Chacha20.Vec
module Loop = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

/// (vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16]


unfold
let op_Array_Access (#w:lanes) (a:uint32xN w) i = (vec_v a).[i]


val transposewxf_f_lemma:
    #w:lanes -> n:nat{pow2 n == w} -> i:nat{i < n} -> vs:lseq (uint32xN w) w
  -> j:nat{j < pow2 i} -> k:nat{k < w / (2 * pow2 i)} ->
  Lemma (let m2 = pow2 i in let m = 2 * m2 in let vs_kj = vs.[k * m + j] in
    Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
    (transposewxw_f #w n i vs).[k * m + j] == vec_interleave_low_n m2 vs_kj vs.[k * m + j + m2] /\
    (transposewxw_f #w n i vs).[k * m + j + m2] == vec_interleave_high_n m2 vs_kj vs.[k * m + j + m2])

let transposewxf_f_lemma #w n i vs j k = admit()

// val lemma_aux: #w:pos -> n:nat{pow2 n == w} -> i:nat{i < n} -> l:nat{l < w} -> Lemma
//   (let m2 = pow2 i in let m = 2 * m2 in
//    let k = l / m in let j = l % m in
//    let j' = if j > m2 then j - m2 else j in
//    l == (if j > m2 then k * m + j' + m2 else k * m + j'))
// let lemma_aux #w n i l = ()

val lemma_k_lt_wm: #w:pos -> n:nat{pow2 n == w} -> i:nat{i < n} -> l:nat{l < w} -> Lemma
  (let m2 = pow2 i in let m = 2 * m2 in l / m < w / m)
let lemma_k_lt_wm #w n i l =
  let m2 = pow2 i in let m = 2 * m2 in
  Math.Lemmas.pow2_plus 1 i;
  assert (m == pow2 (i + 1));
  let k = l / m in
  assert (l < pow2 n);
  Math.Lemmas.lemma_div_lt_nat l n (i + 1);
  assert (l / m < pow2 (n - i - 1));
  Math.Lemmas.pow2_minus n (i + 1);
  assert (k < w / m)


val lemma_l_plus_m2_lt: #w:pos -> n:nat{pow2 n == w} -> i:nat{i < n} -> l:nat{l < w} -> Lemma
  (requires l % (2 * pow2 i) < pow2 i)
  (ensures  (let m2 = pow2 i in let m = 2 * m2 in l / m * m + l % m + pow2 i < pow2 n))
let lemma_l_plus_m2_lt #w n i l =
  let m2 = pow2 i in let m = 2 * m2 in
  let k = l / m in let j = l % m in
  lemma_k_lt_wm #w n i l;
  assert (k < w / m);
  assert (j < m2);
  assert (k * m + j + m2 < k * m + m);
  assert (k * m + j + m2 < (k + 1) * m);
  assert ((k + 1) * m <= w / m * m);
  assert (k * m + j + m2 < w / m * m)


val transposewxw_f_lemma_l:
  #w:lanes -> n:nat{pow2 n == w} -> i:nat{i < n} -> vs:lseq (uint32xN w) w -> l:nat{l < w} -> Lemma
  (if l % (2 * pow2 i) < pow2 i then begin
    lemma_l_plus_m2_lt #w n i l;
    Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
    (transposewxw_f #w n i vs).[l] == vec_interleave_low_n (pow2 i) vs.[l] vs.[l + pow2 i] end
   else begin
    Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
    (transposewxw_f #w n i vs).[l] == vec_interleave_high_n (pow2 i) vs.[l - pow2 i] vs.[l] end)

let transposewxw_f_lemma_l #w n i vs l =
  let m2 = pow2 i in
  let m = 2 * m2 in
  let k = l / m in
  if l % (2 * pow2 i) < pow2 i then begin
    let j = l % m in
    lemma_k_lt_wm #w n i l;
    transposewxf_f_lemma #w n i vs j k end
  else begin
    let j = l % m - m2 in
    lemma_k_lt_wm #w n i l;
    transposewxf_f_lemma #w n i vs j k end


val transpose4x4_lemma_ij: vs:lseq (uint32xN 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4 vs).[i]).[j] == (vec_v vs.[j]).[i])
let transpose4x4_lemma_ij vs i j =
  let res = transposewxw 2 vs in
  Loop.unfold_repeati 2 (transposewxw_f 2) vs 1;
  Loop.unfold_repeati 2 (transposewxw_f 2) vs 0;
  Loop.eq_repeati0 2 (transposewxw_f 2) vs;

  let res0 = transposewxw_f 2 0 vs in
  let res1 = transposewxw_f 2 1 res0 in
  Classical.forall_intro (transposewxw_f_lemma_l #4 2 1 res0);
  Classical.forall_intro (transposewxw_f_lemma_l #4 2 0 vs);

  vec_interleave_low_n_lemma_uint32_4_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[0] res0.[2];

  vec_interleave_low_n_lemma_uint32_4_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[1] res0.[3];

  vec_interleave_low_lemma_uint32_4 vs.[0] vs.[1];
  vec_interleave_high_lemma_uint32_4 vs.[0] vs.[1];

  vec_interleave_low_lemma_uint32_4 vs.[2] vs.[3];
  vec_interleave_high_lemma_uint32_4 vs.[2] vs.[3]


val transpose8x8_lemma_ij: vs:lseq (uint32xN 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma ((vec_v (transpose8x8 vs).[i]).[j] == (vec_v vs.[j]).[i])
let transpose8x8_lemma_ij vs i j =
  let res = transposewxw 3 vs in
  Loop.unfold_repeati 3 (transposewxw_f 3) vs 2;
  Loop.unfold_repeati 3 (transposewxw_f 3) vs 1;
  Loop.unfold_repeati 3 (transposewxw_f 3) vs 0;
  Loop.eq_repeati0 3 (transposewxw_f 3) vs;

  let res0 = transposewxw_f 3 0 vs in
  let res1 = transposewxw_f 3 1 res0 in
  let res2 = transposewxw_f 3 2 res1 in

  Classical.forall_intro (transposewxw_f_lemma_l #8 3 2 res1);
  Classical.forall_intro (transposewxw_f_lemma_l #8 3 1 res0);
  Classical.forall_intro (transposewxw_f_lemma_l #8 3 0 vs);

  vec_interleave_low_n_lemma_uint32_8_4 res1.[0] res1.[4];
  vec_interleave_low_n_lemma_uint32_8_4 res1.[1] res1.[5];
  vec_interleave_low_n_lemma_uint32_8_4 res1.[2] res1.[6];
  vec_interleave_low_n_lemma_uint32_8_4 res1.[3] res1.[7];
  vec_interleave_high_n_lemma_uint32_8_4 res1.[0] res1.[4];
  vec_interleave_high_n_lemma_uint32_8_4 res1.[1] res1.[5];
  vec_interleave_high_n_lemma_uint32_8_4 res1.[2] res1.[6];
  vec_interleave_high_n_lemma_uint32_8_4 res1.[3] res1.[7];

  vec_interleave_low_n_lemma_uint32_8_2 res0.[0] res0.[2];
  vec_interleave_low_n_lemma_uint32_8_2 res0.[1] res0.[3];
  vec_interleave_low_n_lemma_uint32_8_2 res0.[4] res0.[6];
  vec_interleave_low_n_lemma_uint32_8_2 res0.[5] res0.[7];
  vec_interleave_high_n_lemma_uint32_8_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint32_8_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint32_8_2 res0.[4] res0.[6];
  vec_interleave_high_n_lemma_uint32_8_2 res0.[5] res0.[7];

  vec_interleave_low_lemma_uint32_8 vs.[0] vs.[1];
  vec_interleave_low_lemma_uint32_8 vs.[2] vs.[3];
  vec_interleave_low_lemma_uint32_8 vs.[4] vs.[5];
  vec_interleave_low_lemma_uint32_8 vs.[6] vs.[7];
  vec_interleave_high_lemma_uint32_8 vs.[0] vs.[1];
  vec_interleave_high_lemma_uint32_8 vs.[2] vs.[3];
  vec_interleave_high_lemma_uint32_8 vs.[4] vs.[5];
  vec_interleave_high_lemma_uint32_8 vs.[6] vs.[7]


#set-options "--z3rlimit 300"

val transpose16x16_lemma_ij: vs:lseq (uint32xN 16) 16 -> i:nat{i < 16} -> j:nat{j < 16} ->
  Lemma ((vec_v (transpose16x16 vs).[i]).[j] == (vec_v vs.[j]).[i])
let transpose16x16_lemma_ij vs i j =
  let res = transposewxw 4 vs in
  Loop.unfold_repeati 4 (transposewxw_f 4) vs 3;
  Loop.unfold_repeati 4 (transposewxw_f 4) vs 2;
  Loop.unfold_repeati 4 (transposewxw_f 4) vs 1;
  Loop.unfold_repeati 4 (transposewxw_f 4) vs 0;
  Loop.eq_repeati0 4 (transposewxw_f 4) vs;

  let res0 = transposewxw_f 4 0 vs in
  let res1 = transposewxw_f 4 1 res0 in
  let res2 = transposewxw_f 4 2 res1 in
  let res3 = transposewxw_f 4 3 res2 in

  Classical.forall_intro (transposewxw_f_lemma_l #16 4 3 res2);
  Classical.forall_intro (transposewxw_f_lemma_l #16 4 2 res1);
  Classical.forall_intro (transposewxw_f_lemma_l #16 4 1 res0);
  Classical.forall_intro (transposewxw_f_lemma_l #16 4 0 vs);

  vec_interleave_low_n_lemma_uint32_16_8 res2.[0] res2.[8];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[1] res2.[9];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[2] res2.[10];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[3] res2.[11];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[4] res2.[12];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[5] res2.[13];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[6] res2.[14];
  vec_interleave_low_n_lemma_uint32_16_8 res2.[7] res2.[15];

  vec_interleave_high_n_lemma_uint32_16_8 res2.[0] res2.[8];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[1] res2.[9];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[2] res2.[10];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[3] res2.[11];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[4] res2.[12];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[5] res2.[13];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[6] res2.[14];
  vec_interleave_high_n_lemma_uint32_16_8 res2.[7] res2.[15];

  vec_interleave_low_n_lemma_uint32_16_4 res1.[0] res1.[4];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[1] res1.[5];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[2] res1.[6];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[3] res1.[7];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[8] res1.[12];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[9] res1.[13];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[10] res1.[14];
  vec_interleave_low_n_lemma_uint32_16_4 res1.[11] res1.[15];

  vec_interleave_high_n_lemma_uint32_16_4 res1.[0] res1.[4];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[1] res1.[5];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[2] res1.[6];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[3] res1.[7];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[8] res1.[12];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[9] res1.[13];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[10] res1.[14];
  vec_interleave_high_n_lemma_uint32_16_4 res1.[11] res1.[15];

  vec_interleave_low_n_lemma_uint32_16_2 res0.[0] res0.[2];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[1] res0.[3];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[4] res0.[6];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[5] res0.[7];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[8] res0.[10];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[9] res0.[11];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[12] res0.[14];
  vec_interleave_low_n_lemma_uint32_16_2 res0.[13] res0.[15];

  vec_interleave_high_n_lemma_uint32_16_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[4] res0.[6];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[5] res0.[7];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[8] res0.[10];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[9] res0.[11];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[12] res0.[14];
  vec_interleave_high_n_lemma_uint32_16_2 res0.[13] res0.[15];

  vec_interleave_low_lemma_uint32_16 vs.[0] vs.[1];
  vec_interleave_low_lemma_uint32_16 vs.[2] vs.[3];
  vec_interleave_low_lemma_uint32_16 vs.[4] vs.[5];
  vec_interleave_low_lemma_uint32_16 vs.[6] vs.[7];
  vec_interleave_low_lemma_uint32_16 vs.[8] vs.[9];
  vec_interleave_low_lemma_uint32_16 vs.[10] vs.[11];
  vec_interleave_low_lemma_uint32_16 vs.[12] vs.[13];
  vec_interleave_low_lemma_uint32_16 vs.[14] vs.[15];

  vec_interleave_high_lemma_uint32_16 vs.[0] vs.[1];
  vec_interleave_high_lemma_uint32_16 vs.[2] vs.[3];
  vec_interleave_high_lemma_uint32_16 vs.[4] vs.[5];
  vec_interleave_high_lemma_uint32_16 vs.[6] vs.[7];
  vec_interleave_high_lemma_uint32_16 vs.[8] vs.[9];
  vec_interleave_high_lemma_uint32_16 vs.[10] vs.[11];
  vec_interleave_high_lemma_uint32_16 vs.[12] vs.[13];
  vec_interleave_high_lemma_uint32_16 vs.[14] vs.[15]


#set-options "--z3rlimit 50"

val transpose4x4_lemma: vs:lseq (uint32xN 4) 4 ->
  Lemma ((forall (i:nat{i < 4}) (j:nat{j < 4}). (vec_v (transpose4x4 vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose4x4_lemma vs =
  Classical.forall_intro_2 (transpose4x4_lemma_ij vs)

val transpose8x8_lemma: vs:lseq (uint32xN 8) 8 ->
  Lemma ((forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v (transpose8x8 vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose8x8_lemma vs =
  Classical.forall_intro_2 (transpose8x8_lemma_ij vs)

val transpose16x16_lemma: vs:lseq (uint32xN 16) 16 ->
  Lemma ((forall (i:nat{i < 16}) (j:nat{j < 16}). (vec_v (transpose16x16 vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose16x16_lemma vs =
  Classical.forall_intro_2 (transpose16x16_lemma_ij vs)



val transpose4_lemma: k:state 4 -> i:nat{i < 16 * 4} ->
  Lemma ((vec_v (transpose4 k).[i / 4]).[i % 4] == ((transpose_state k).[i / 16]).[i % 16])
let transpose4_lemma st i =
  let r0 = transpose4x4 (sub st 0 4) in
  transpose4x4_lemma (sub st 0 4);
  let r1 = transpose4x4 (sub st 4 4) in
  transpose4x4_lemma (sub st 4 4);
  let r2 = transpose4x4 (sub st 8 4) in
  transpose4x4_lemma (sub st 8 4);
  let r3 = transpose4x4 (sub st 12 4) in
  transpose4x4_lemma (sub st 12 4);
  let (v0,v1,v2,v3)     = (r0.[0], r0.[1], r0.[2], r0.[3]) in
  let (v4,v5,v6,v7)     = (r1.[0], r1.[1], r1.[2], r1.[3]) in
  let (v8,v9,v10,v11)   = (r2.[0], r2.[1], r2.[2], r2.[3]) in
  let (v12,v13,v14,v15) = (r3.[0], r3.[1], r3.[2], r3.[3]) in
  let res : lseq (uint32xN 4) 16 = create16 v0 v4 v8 v12 v1 v5 v9 v13 v2 v6 v10 v14 v3 v7 v11 v15 in
  ()


val transpose8_lemma: k:state 8 -> i:nat{i < 16 * 8} ->
  Lemma ((vec_v (transpose8 k).[i / 8]).[i % 8] == ((transpose_state k).[i / 16]).[i % 16])
let transpose8_lemma st i =
  let r0 = transpose8x8 (sub st 0 8) in
  transpose8x8_lemma (sub st 0 8);
  let r1 = transpose8x8 (sub st 8 8) in
  transpose8x8_lemma (sub st 8 8);
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (r0.[0],r0.[1],r0.[2],r0.[3],r0.[4],r0.[5],r0.[6],r0.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (r1.[0],r1.[1],r1.[2],r1.[3],r1.[4],r1.[5],r1.[6],r1.[7]) in
  let res : lseq (uint32xN 8) 16 = create16 v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15 in
  ()


val transpose16_lemma: k:state 16 -> i:nat{i < 16 * 16} ->
  Lemma ((vec_v (transpose16 k).[i / 16]).[i % 16] == ((transpose_state k).[i / 16]).[i % 16])
let transpose16_lemma k i =
  transpose16x16_lemma k


val transpose_lemma_index: #w:lanes -> k:state w -> i:nat{i < 16 * w} ->
  Lemma ((vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i
  | 16 -> transpose16_lemma k i
