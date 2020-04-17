module Lib.IntVector.Transpose

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  transpose4x4
///

inline_for_extraction noextract
val transpose4x4_uint32: #t:v_inttype{t == U32} -> vec_t4 t -> vec_t4 t
let transpose4x4_uint32 #t vs =
  let (v0,v1,v2,v3) = vs in
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  (v0'',v1'',v2'',v3'')


let transpose4x4 #t vs =
  match t with
  | U32 -> transpose4x4_uint32 #t vs
  | _ -> admit()

///
///   transpose8x8
///

inline_for_extraction noextract
val transpose8x8_uint32_0: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32_0 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction noextract
val transpose8x8_uint32_1: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32_1 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low_n 2 v0 v2 in
  let v2' = vec_interleave_high_n 2 v0 v2 in
  let v1' = vec_interleave_low_n 2 v1 v3 in
  let v3' = vec_interleave_high_n 2 v1 v3 in
  let v4' = vec_interleave_low_n 2 v4 v6 in
  let v6' = vec_interleave_high_n 2 v4 v6 in
  let v5' = vec_interleave_low_n 2 v5 v7 in
  let v7' = vec_interleave_high_n 2 v5 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction noextract
val transpose8x8_uint32_2: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32_2 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low_n 4 v0 v4 in
  let v4' = vec_interleave_high_n 4 v0 v4 in
  let v1' = vec_interleave_low_n 4 v1 v5 in
  let v5' = vec_interleave_high_n 4 v1 v5 in
  let v2' = vec_interleave_low_n 4 v2 v6 in
  let v6' = vec_interleave_high_n 4 v2 v6 in
  let v3' = vec_interleave_low_n 4 v3 v7 in
  let v7' = vec_interleave_high_n 4 v3 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction noextract
val transpose8x8_uint32: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32 #t vs0 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = vs0 in
  [@inline_let]
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_uint32_0 #t (v0,v1,v2,v3,v4,v5,v6,v7) in
  [@inline_let]
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_uint32_1 #t (v0',v1',v2',v3',v4',v5',v6',v7') in
  [@inline_let]
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_uint32_2 #t (v0',v1',v2',v3',v4',v5',v6',v7') in
  (v0',v2',v1',v3',v4',v6',v5',v7')

let transpose8x8 #t vs =
  match t with
  | U32 -> transpose8x8_uint32 #t vs
  | _ -> admit()


inline_for_extraction noextract
val transpose16x16_uint32_0: #t:v_inttype{t == U32} -> vs:(vec_t16 t & vec_t16 t) -> (vec_t16 t & vec_t16 t)
let transpose16x16_uint32_0 #t vs =
  let ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) = vs in

  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in
  let v8' = vec_interleave_low v8 v9 in
  let v9' = vec_interleave_high v8 v9 in
  let v10' = vec_interleave_low v10 v11 in
  let v11' = vec_interleave_high v10 v11 in
  let v12' = vec_interleave_low v12 v13 in
  let v13' = vec_interleave_high v12 v13 in
  let v14' = vec_interleave_low v14 v15 in
  let v15' = vec_interleave_high v14 v15 in

  ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15'))


inline_for_extraction noextract
val transpose16x16_uint32_1: #t:v_inttype{t == U32} -> vs:(vec_t16 t & vec_t16 t) -> (vec_t16 t & vec_t16 t)
let transpose16x16_uint32_1 #t vs =
  let ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) = vs in

  let v0' = vec_interleave_low_n 2 v0 v2 in
  let v2' = vec_interleave_high_n 2 v0 v2 in
  let v1' = vec_interleave_low_n 2 v1 v3 in
  let v3' = vec_interleave_high_n 2 v1 v3 in
  let v4' = vec_interleave_low_n 2 v4 v6 in
  let v6' = vec_interleave_high_n 2 v4 v6 in
  let v5' = vec_interleave_low_n 2 v5 v7 in
  let v7' = vec_interleave_high_n 2 v5 v7 in
  let v8' = vec_interleave_low_n 2 v8 v10 in
  let v10' = vec_interleave_high_n 2 v8 v10 in
  let v9' = vec_interleave_low_n 2 v9 v11 in
  let v11' = vec_interleave_high_n 2 v9 v11 in
  let v12' = vec_interleave_low_n 2 v12 v14 in
  let v14' = vec_interleave_high_n 2 v12 v14 in
  let v13' = vec_interleave_low_n 2 v13 v15 in
  let v15' = vec_interleave_high_n 2 v13 v15 in

  ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15'))


inline_for_extraction noextract
val transpose16x16_uint32_2: #t:v_inttype{t == U32} -> vs:(vec_t16 t & vec_t16 t) -> (vec_t16 t & vec_t16 t)
let transpose16x16_uint32_2 #t vs =
  let ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) = vs in

  let v0' = vec_interleave_low_n 4 v0 v4 in
  let v4' = vec_interleave_high_n 4 v0 v4 in
  let v1' = vec_interleave_low_n 4 v1 v5 in
  let v5' = vec_interleave_high_n 4 v1 v5 in
  let v2' = vec_interleave_low_n 4 v2 v6 in
  let v6' = vec_interleave_high_n 4 v2 v6 in
  let v3' = vec_interleave_low_n 4 v3 v7 in
  let v7' = vec_interleave_high_n 4 v3 v7 in
  let v8' = vec_interleave_low_n 4 v8 v12 in
  let v12' = vec_interleave_high_n 4 v8 v12 in
  let v9' = vec_interleave_low_n 4 v9 v13 in
  let v13' = vec_interleave_high_n 4 v9 v13 in
  let v10' = vec_interleave_low_n 4 v10 v14 in
  let v14' = vec_interleave_high_n 4 v10 v14 in
  let v11' = vec_interleave_low_n 4 v11 v15 in
  let v15' = vec_interleave_high_n 4 v11 v15 in

  ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15'))


inline_for_extraction noextract
val transpose16x16_uint32_3: #t:v_inttype{t == U32} -> vs:(vec_t16 t & vec_t16 t) -> (vec_t16 t & vec_t16 t)
let transpose16x16_uint32_3 #t vs =
  let ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) = vs in

  let v0' = vec_interleave_low_n 8 v0 v8 in
  let v8' = vec_interleave_high_n 8 v0 v8 in
  let v1' = vec_interleave_low_n 8 v1 v9 in
  let v9' = vec_interleave_high_n 8 v1 v9 in
  let v2' = vec_interleave_low_n 8 v2 v10 in
  let v10' = vec_interleave_high_n 8 v2 v10 in
  let v3' = vec_interleave_low_n 8 v3 v11 in
  let v11' = vec_interleave_high_n 8 v3 v11 in
  let v4' = vec_interleave_low_n 8 v4 v12 in
  let v12' = vec_interleave_high_n 8 v4 v12 in
  let v5' = vec_interleave_low_n 8 v5 v13 in
  let v13' = vec_interleave_high_n 8 v5 v13 in
  let v6' = vec_interleave_low_n 8 v6 v14 in
  let v14' = vec_interleave_high_n 8 v6 v14 in
  let v7' = vec_interleave_low_n 8 v7 v15 in
  let v15' = vec_interleave_high_n 8 v7 v15 in

  ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15'))


inline_for_extraction noextract
val transpose16x16_uint32: #t:v_inttype{t == U32} -> vs:(vec_t16 t & vec_t16 t) -> (vec_t16 t & vec_t16 t)
let transpose16x16_uint32 #t vs =
  let ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) = vs in

  [@inline_let]
  let ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) =
    transpose16x16_uint32_0 ((v0,v1,v2,v3,v4,v5,v6,v7),(v8,v9,v10,v11,v12,v13,v14,v15)) in
  [@inline_let]
  let ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) =
    transpose16x16_uint32_1 ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) in
  [@inline_let]
  let ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) =
    transpose16x16_uint32_2 ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) in
  [@inline_let]
  let ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) =
    transpose16x16_uint32_3 ((v0',v1',v2',v3',v4',v5',v6',v7'),(v8',v9',v10',v11',v12',v13',v14',v15')) in

  ((v0',v2',v1',v3',v4',v6',v5',v7'),(v8',v10',v9',v11',v12',v14',v13',v15'))


let transpose16x16 #t vs =
  match t with
  | U32 -> transpose16x16_uint32 #t vs
  | _ -> admit()


///
///  generic transpose
///

inline_for_extraction noextract
val transposewxw_uint32_f_l:
    #w:width
  -> n:nat{pow2 n == w}
  -> i:nat{i < n}
  -> lseq (vec_t U32 w) w
  -> l:nat{l < w} ->
  vec_t U32 w

let transposewxw_uint32_f_l #w n i vs l =
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
  if l % (2 * pow2 i) < pow2 i
  then begin
    assume (l + pow2 i < w);
    vec_interleave_low_n (pow2 i) vs.[l] vs.[l + pow2 i] end
  else
    vec_interleave_high_n (pow2 i) vs.[l - pow2 i] vs.[l]


inline_for_extraction noextract
val transposewxw_uint32_f: #w:width -> n:nat{pow2 n == w} -> i:nat{i < n} -> lseq (vec_t U32 w) w -> lseq (vec_t U32 w) w
let transposewxw_uint32_f #w n i vs =
  createi w (transposewxw_uint32_f_l #w n i vs)

val transposewxw_uint32_lseq: #w:width -> n:nat{pow2 n == w} -> vs:lseq (vec_t U32 w) w -> lseq (vec_t U32 w) w
let transposewxw_uint32_lseq #w n vs =
  Loops.repeati n (transposewxw_uint32_f #w n) vs

///
///  transposewxw_lseq lemmas
///
val transpose4x4_lseq_is_transposewxw_uint32: vs:lseq (vec_t U32 4) 4 ->
  Lemma
   (let r = transposewxw_uint32_lseq 2 vs in
    create4 r.[0] r.[2] r.[1] r.[3] `Seq.equal` transpose4x4_lseq #U32 vs)

let transpose4x4_lseq_is_transposewxw_uint32 vs0 =
  let n = 2 in
  Loops.unfold_repeati n (transposewxw_uint32_f #4 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_uint32_f #4 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_uint32_f #4 n) vs0


inline_for_extraction noextract
let f_lseq8 (#t:v_inttype) (vs:lseq (vec_t t 8) 8) (f:vec_t8 t -> vec_t8 t) : lseq (vec_t t 8) 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (r0,r1,r2,r3,r4,r5,r6,r7) = f (v0,v1,v2,v3,v4,v5,v6,v7) in
  create8 r0 r1 r2 r3 r4 r5 r6 r7


val transpose8x8_lseq_is_transposewxw_uint32: vs:lseq (vec_t U32 8) 8 ->
  Lemma
   (let r = transposewxw_uint32_lseq 3 vs in
    create8 r.[0] r.[2] r.[1] r.[3] r.[4] r.[6] r.[5] r.[7] `Seq.equal` transpose8x8_lseq #U32 vs)

let transpose8x8_lseq_is_transposewxw_uint32 vs0 =
  let n = 3 in
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 2;
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_uint32_f #8 n) vs0;
  let r = transposewxw_uint32_lseq 3 vs0 in
  let res = create8 r.[0] r.[2] r.[1] r.[3] r.[4] r.[6] r.[5] r.[7] in

  let res0 = transposewxw_uint32_f n 0 vs0 in
  eq_intro res0 (f_lseq8 vs0 transpose8x8_uint32_0);
  let res1 = transposewxw_uint32_f n 1 res0 in
  eq_intro res1 (f_lseq8 res0 transpose8x8_uint32_1);
  let res2 = transposewxw_uint32_f n 2 res1 in
  eq_intro res2 (f_lseq8 res1 transpose8x8_uint32_2);
  eq_intro res (f_lseq8 vs0 transpose8x8)


inline_for_extraction noextract
let f_lseq16 (#t:v_inttype) (vs:lseq (vec_t t 16) 16)
  (f:(vec_t16 t & vec_t16 t -> vec_t16 t & vec_t16 t)) : lseq (vec_t t 16) 16
 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (vs.[8],vs.[9],vs.[10],vs.[11],vs.[12],vs.[13],vs.[14],vs.[15]) in
  let ((r0,r1,r2,r3,r4,r5,r6,r7),(r8,r9,r10,r11,r12,r13,r14,r15)) =
    f ((v0,v1,v2,v3,v4,v5,v6,v7), (v8,v9,v10,v11,v12,v13,v14,v15)) in
  create16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15


val transpose16x16_lseq_is_transposewxw_uint32: vs:lseq (vec_t U32 16) 16 ->
  Lemma
   (let r = transposewxw_uint32_lseq 4 vs in
    create16 r.[0] r.[2] r.[1] r.[3] r.[4] r.[6] r.[5] r.[7] r.[8] r.[10] r.[9] r.[11] r.[12] r.[14] r.[13] r.[15]
      `Seq.equal` transpose16x16_lseq #U32 vs)

let transpose16x16_lseq_is_transposewxw_uint32 vs0 =
  let n = 4 in
  Loops.unfold_repeati n (transposewxw_uint32_f #16 n) vs0 3;
  Loops.unfold_repeati n (transposewxw_uint32_f #16 n) vs0 2;
  Loops.unfold_repeati n (transposewxw_uint32_f #16 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_uint32_f #16 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_uint32_f #16 n) vs0;
  let r = transposewxw_uint32_lseq n vs0 in

  let res0 = transposewxw_uint32_f n 0 vs0 in
  eq_intro res0 (f_lseq16 vs0 transpose16x16_uint32_0);
  let res1 = transposewxw_uint32_f n 1 res0 in
  eq_intro res1 (f_lseq16 res0 transpose16x16_uint32_1);
  let res2 = transposewxw_uint32_f n 2 res1 in
  eq_intro res2 (f_lseq16 res1 transpose16x16_uint32_2);
  let res3 = transposewxw_uint32_f n 3 res2 in
  eq_intro res3 (f_lseq16 res2 transpose16x16_uint32_3);
  let res = create16 r.[0] r.[2] r.[1] r.[3] r.[4] r.[6] r.[5] r.[7] r.[8] r.[10] r.[9] r.[11] r.[12] r.[14] r.[13] r.[15] in
  eq_intro res (f_lseq16 vs0 transpose16x16_uint32)


val transpose4x4_lemma_ij: vs:lseq (vec_t U32 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4_lseq #U32 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose4x4_lemma_ij vs0 i j =
  transpose4x4_lseq_is_transposewxw_uint32 vs0;
  let n = 2 in
  let r = transposewxw_uint32_lseq 2 vs0 in
  Loops.unfold_repeati n (transposewxw_uint32_f #4 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_uint32_f #4 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_uint32_f #4 n) vs0;

  let res0 = transposewxw_uint32_f 2 0 vs0 in
  let res1 = transposewxw_uint32_f 2 1 res0 in

  vec_interleave_low_n_lemma_uint32_4_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[0] res0.[2];
  vec_interleave_low_n_lemma_uint32_4_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[1] res0.[3];

  vec_interleave_low_lemma_uint32_4 vs0.[0] vs0.[1];
  vec_interleave_high_lemma_uint32_4 vs0.[0] vs0.[1];
  vec_interleave_low_lemma_uint32_4 vs0.[2] vs0.[3];
  vec_interleave_high_lemma_uint32_4 vs0.[2] vs0.[3]


val transpose8x8_lemma_ij: vs:lseq (vec_t U32 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma ((vec_v (transpose8x8_lseq #U32 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose8x8_lemma_ij vs0 i j =
  transpose8x8_lseq_is_transposewxw_uint32 vs0;
  let n = 3 in
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 2;
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_uint32_f #8 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_uint32_f #8 n) vs0;

  let res0 = transposewxw_uint32_f n 0 vs0 in
  let res1 = transposewxw_uint32_f n 1 res0 in
  let res2 = transposewxw_uint32_f n 2 res1 in

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

  vec_interleave_low_lemma_uint32_8 vs0.[0] vs0.[1];
  vec_interleave_low_lemma_uint32_8 vs0.[2] vs0.[3];
  vec_interleave_low_lemma_uint32_8 vs0.[4] vs0.[5];
  vec_interleave_low_lemma_uint32_8 vs0.[6] vs0.[7];
  vec_interleave_high_lemma_uint32_8 vs0.[0] vs0.[1];
  vec_interleave_high_lemma_uint32_8 vs0.[2] vs0.[3];
  vec_interleave_high_lemma_uint32_8 vs0.[4] vs0.[5];
  vec_interleave_high_lemma_uint32_8 vs0.[6] vs0.[7]


val transpose16x16_lemma_ij: vs:lseq (vec_t U32 16) 16 -> i:nat{i < 16} -> j:nat{j < 16} ->
  Lemma ((vec_v (transpose16x16_lseq #U32 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose16x16_lemma_ij vs0 i j =
  transpose16x16_lseq_is_transposewxw_uint32 vs0;

  Loops.unfold_repeati 4 (transposewxw_uint32_f 4) vs0 3;
  Loops.unfold_repeati 4 (transposewxw_uint32_f 4) vs0 2;
  Loops.unfold_repeati 4 (transposewxw_uint32_f 4) vs0 1;
  Loops.unfold_repeati 4 (transposewxw_uint32_f 4) vs0 0;
  Loops.eq_repeati0 4 (transposewxw_uint32_f 4) vs0;

  let res0 = transposewxw_uint32_f 4 0 vs0 in
  let res1 = transposewxw_uint32_f 4 1 res0 in
  let res2 = transposewxw_uint32_f 4 2 res1 in
  let res3 = transposewxw_uint32_f 4 3 res2 in

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

  vec_interleave_low_lemma_uint32_16 vs0.[0] vs0.[1];
  vec_interleave_low_lemma_uint32_16 vs0.[2] vs0.[3];
  vec_interleave_low_lemma_uint32_16 vs0.[4] vs0.[5];
  vec_interleave_low_lemma_uint32_16 vs0.[6] vs0.[7];
  vec_interleave_low_lemma_uint32_16 vs0.[8] vs0.[9];
  vec_interleave_low_lemma_uint32_16 vs0.[10] vs0.[11];
  vec_interleave_low_lemma_uint32_16 vs0.[12] vs0.[13];
  vec_interleave_low_lemma_uint32_16 vs0.[14] vs0.[15];

  vec_interleave_high_lemma_uint32_16 vs0.[0] vs0.[1];
  vec_interleave_high_lemma_uint32_16 vs0.[2] vs0.[3];
  vec_interleave_high_lemma_uint32_16 vs0.[4] vs0.[5];
  vec_interleave_high_lemma_uint32_16 vs0.[6] vs0.[7];
  vec_interleave_high_lemma_uint32_16 vs0.[8] vs0.[9];
  vec_interleave_high_lemma_uint32_16 vs0.[10] vs0.[11];
  vec_interleave_high_lemma_uint32_16 vs0.[12] vs0.[13];
  vec_interleave_high_lemma_uint32_16 vs0.[14] vs0.[15]


let transpose4x4_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose4x4_lemma_ij vs)
  | _ -> admit()

let transpose8x8_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose8x8_lemma_ij vs)
  | _ -> admit()

let transpose16x16_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose16x16_lemma_ij vs)
  | _ -> admit()
