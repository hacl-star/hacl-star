module Lib.IntVector.Transpose

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  transpose4x4
///

inline_for_extraction
val transpose4x4_0: #t:v_inttype -> vec_t4 t -> vec_t4 t
let transpose4x4_0 #t (v0,v1,v2,v3) =
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  (v0'',v2'',v1'',v3'')


inline_for_extraction
val transpose4x4_uint32: #t:v_inttype{t == U32} -> vec_t4 t -> vec_t4 t
let transpose4x4_uint32 #t vs =
  let (v0'',v2'',v1'',v3'') = transpose4x4_0 #t vs in
  (v0'',v1'',v2'',v3'')


inline_for_extraction
val transpose4x4_uint64: #t:v_inttype{t == U64} -> vec_t4 t -> vec_t4 t
let transpose4x4_uint64 #t vs = transpose4x4_0 #t vs


let transpose4x4 #t vs =
  match t with
  | U32 -> transpose4x4_uint32 #t vs
  | U64 -> transpose4x4_uint64 #t vs

///
///   transpose8x8
///

inline_for_extraction
val transpose8x8_0: #t:v_inttype -> vec_t8 t -> vec_t8 t
let transpose8x8_0 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction
val transpose8x8_1: #t:v_inttype -> vec_t8 t -> vec_t8 t
let transpose8x8_1 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low_n 2 v0 v2 in
  let v2' = vec_interleave_high_n 2 v0 v2 in
  let v1' = vec_interleave_low_n 2 v1 v3 in
  let v3' = vec_interleave_high_n 2 v1 v3 in
  let v4' = vec_interleave_low_n 2 v4 v6 in
  let v6' = vec_interleave_high_n 2 v4 v6 in
  let v5' = vec_interleave_low_n 2 v5 v7 in
  let v7' = vec_interleave_high_n 2 v5 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction
val transpose8x8_2: #t:v_inttype -> vec_t8 t -> vec_t8 t
let transpose8x8_2 #t (v0,v1,v2,v3,v4,v5,v6,v7) =
  let v0' = vec_interleave_low_n 4 v0 v4 in
  let v4' = vec_interleave_high_n 4 v0 v4 in
  let v1' = vec_interleave_low_n 4 v1 v5 in
  let v5' = vec_interleave_high_n 4 v1 v5 in
  let v2' = vec_interleave_low_n 4 v2 v6 in
  let v6' = vec_interleave_high_n 4 v2 v6 in
  let v3' = vec_interleave_low_n 4 v3 v7 in
  let v7' = vec_interleave_high_n 4 v3 v7 in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction
val transpose8x8_012: #t:v_inttype -> vec_t8 t -> vec_t8 t
let transpose8x8_012 #t vs0 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = vs0 in
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_0 #t (v0,v1,v2,v3,v4,v5,v6,v7) in
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_1 #t (v0',v1',v2',v3',v4',v5',v6',v7') in
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_2 #t (v0',v1',v2',v3',v4',v5',v6',v7') in
  (v0',v1',v2',v3',v4',v5',v6',v7')


inline_for_extraction
val transpose8x8_uint32: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32 #t vs0 =
  let (v0',v1',v2',v3',v4',v5',v6',v7') = transpose8x8_012 #t vs0 in
  (v0',v2',v1',v3',v4',v6',v5',v7')


let transpose8x8 #t vs =
  match t with
  | U32 -> transpose8x8_uint32 #t vs

///
///  generic transpose
///

val lemma_l_plus_pow2i_lt: #w:pos -> n:nat{pow2 n == w} -> i:nat{i < n} -> l:nat{l < w} -> Lemma
  (requires l % (2 * pow2 i) < pow2 i)
  (ensures  l + pow2 i < w)

let lemma_l_plus_pow2i_lt #w n i l =
  let pow2i1 = pow2 (i + 1) in

  calc (<) {
    l + pow2 i;
    (==) { Math.Lemmas.euclidean_division_definition l pow2i1 }
    l / pow2i1 * pow2i1 + l % pow2i1 + pow2 i;
    (==) { Math.Lemmas.pow2_plus 1 i }
    l / pow2i1 * pow2i1 + l % (2 * pow2 i) + pow2 i;
    (<) { assert (l % (2 * pow2 i) < pow2 i) }
    l / pow2i1 * pow2i1 + pow2 i + pow2 i;
    (==) { Math.Lemmas.pow2_double_sum i }
    l / pow2i1 * pow2i1 + pow2i1;
    (==) { Math.Lemmas.distributivity_add_left (l / pow2i1) 1 pow2i1 }
    (l / pow2i1 + 1) * pow2i1;
    (<=) { Math.Lemmas.lemma_div_lt_nat l n (i + 1) }
    pow2 (n - i - 1) * pow2 (i + 1);
    (==) { Math.Lemmas.pow2_plus (n - i - 1) (i + 1) }
    pow2 n;
  }


inline_for_extraction
val transposewxw_f_l:
    #w:width
  -> #t:v_inttype
  -> n:nat{pow2 n == w}
  -> i:nat{i < n}
  -> lseq (vec_t t w) w
  -> l:nat{l < w} ->
  vec_t t w

let transposewxw_f_l #w #t n i vs l =
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
  if l % (2 * pow2 i) < pow2 i
  then begin
    lemma_l_plus_pow2i_lt #w n i l;
    vec_interleave_low_n (pow2 i) vs.[l] vs.[l + pow2 i] end
  else
    vec_interleave_high_n (pow2 i) vs.[l - pow2 i] vs.[l]


inline_for_extraction
val transposewxw_f: #w:width -> #t:v_inttype -> n:nat{pow2 n == w} -> i:nat{i < n} -> lseq (vec_t t w) w -> lseq (vec_t t w) w
let transposewxw_f #w #t n i vs =
  createi w (transposewxw_f_l #w n i vs)

val transposewxw_lseq: #w:width -> #t:v_inttype -> n:nat{pow2 n == w} -> vs:lseq (vec_t t w) w -> lseq (vec_t t w) w
let transposewxw_lseq #w #t n vs =
  Loops.repeati n (transposewxw_f #w n) vs

///
///  transposewxw_lseq lemmas
///

inline_for_extraction
let f_lseq4 (#t:v_inttype) (vs:lseq (vec_t t 4) 4) (f:vec_t4 t -> vec_t4 t) : lseq (vec_t t 4) 4 =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let (r0,r1,r2,r3) = f (v0,v1,v2,v3) in
  create4 r0 r1 r2 r3

val transpose4x4_lseq_is_transposewxw: #t:v_inttype -> vs:lseq (vec_t t 4) 4 ->
  Lemma (transposewxw_lseq 2 vs `Seq.equal` f_lseq4 vs transpose4x4_0)

let transpose4x4_lseq_is_transposewxw #t vs0 =
  let n = 2 in
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_f #4 n) vs0;
  eq_intro (transposewxw_lseq 2 vs0) (f_lseq4 vs0 transpose4x4_0)


inline_for_extraction
let f_lseq8 (#t:v_inttype) (vs:lseq (vec_t t 8) 8) (f:vec_t8 t -> vec_t8 t) : lseq (vec_t t 8) 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (r0,r1,r2,r3,r4,r5,r6,r7) = f (v0,v1,v2,v3,v4,v5,v6,v7) in
  create8 r0 r1 r2 r3 r4 r5 r6 r7


val transpose8x8_lseq_is_transposewxw: #t:v_inttype -> vs:lseq (vec_t t 8) 8 ->
  Lemma (transposewxw_lseq 3 vs `Seq.equal` f_lseq8 vs transpose8x8_012)

let transpose8x8_lseq_is_transposewxw #t vs0 =
  let n = 3 in
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 2;
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_f #8 n) vs0;

  let res0 = transposewxw_f n 0 vs0 in
  eq_intro res0 (f_lseq8 vs0 transpose8x8_0);
  let res1 = transposewxw_f n 1 res0 in
  eq_intro res1 (f_lseq8 res0 transpose8x8_1);
  let res2 = transposewxw_f n 2 res1 in
  eq_intro res2 (f_lseq8 res1 transpose8x8_2);
  eq_intro (transposewxw_lseq 3 vs0) (f_lseq8 vs0 transpose8x8_012)


val transpose4x4_lemma_uint32_ij: vs:lseq (vec_t U32 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4_lseq #U32 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose4x4_lemma_uint32_ij vs0 i j =
  transpose4x4_lseq_is_transposewxw vs0;
  let n = 2 in
  let r = transposewxw_lseq 2 vs0 in
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_f #4 n) vs0;

  let res0 = transposewxw_f 2 0 vs0 in
  let res1 = transposewxw_f 2 1 res0 in

  vec_interleave_low_n_lemma_uint32_4_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[0] res0.[2];
  vec_interleave_low_n_lemma_uint32_4_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint32_4_2 res0.[1] res0.[3];

  vec_interleave_low_lemma_uint32_4 vs0.[0] vs0.[1];
  vec_interleave_high_lemma_uint32_4 vs0.[0] vs0.[1];
  vec_interleave_low_lemma_uint32_4 vs0.[2] vs0.[3];
  vec_interleave_high_lemma_uint32_4 vs0.[2] vs0.[3]


val transpose4x4_lemma_uint64_ij: vs:lseq (vec_t U64 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4_lseq #U64 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose4x4_lemma_uint64_ij vs0 i j =
  transpose4x4_lseq_is_transposewxw vs0;
  let n = 2 in
  let r = transposewxw_lseq 2 vs0 in
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_f #4 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_f #4 n) vs0;

  let res0 = transposewxw_f 2 0 vs0 in
  let res1 = transposewxw_f 2 1 res0 in

  vec_interleave_low_n_lemma_uint64_4_2 res0.[0] res0.[2];
  vec_interleave_high_n_lemma_uint64_4_2 res0.[0] res0.[2];
  vec_interleave_low_n_lemma_uint64_4_2 res0.[1] res0.[3];
  vec_interleave_high_n_lemma_uint64_4_2 res0.[1] res0.[3];

  vec_interleave_low_lemma_uint64_4 vs0.[0] vs0.[1];
  vec_interleave_high_lemma_uint64_4 vs0.[0] vs0.[1];
  vec_interleave_low_lemma_uint64_4 vs0.[2] vs0.[3];
  vec_interleave_high_lemma_uint64_4 vs0.[2] vs0.[3]


val transpose8x8_lemma_uint32_ij: vs:lseq (vec_t U32 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma ((vec_v (transpose8x8_lseq #U32 vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose8x8_lemma_uint32_ij vs0 i j =
  transpose8x8_lseq_is_transposewxw vs0;
  let n = 3 in
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 2;
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 1;
  Loops.unfold_repeati n (transposewxw_f #8 n) vs0 0;
  Loops.eq_repeati0 n (transposewxw_f #8 n) vs0;

  let res0 = transposewxw_f n 0 vs0 in
  let res1 = transposewxw_f n 1 res0 in
  let res2 = transposewxw_f n 2 res1 in

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


let transpose4x4_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose4x4_lemma_uint32_ij vs)
  | U64 -> Classical.forall_intro_2 (transpose4x4_lemma_uint64_ij vs)


let transpose8x8_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose8x8_lemma_uint32_ij vs)
