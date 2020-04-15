module Lib.IntVector.Transpose

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val transposewxw_uint32_f_l:
    #w:width
  -> n:nat{pow2 n == w}
  -> i:nat{i < n}
  -> pow2i:nat{pow2i == pow2 i}
  -> ntuple (vec_t U32 w) w
  -> l:nat{l < w} ->
  vec_t U32 w

let transposewxw_uint32_f_l #w n i pow2i vs l =
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 i n;
  if l % (2 * pow2i) < pow2i
  then begin
    assume (l + pow2i < w);
    vec_interleave_low_n pow2i vs.(|l|) vs.(|l + pow2i|) end
  else
    vec_interleave_high_n pow2i vs.(|l - pow2i|) vs.(|l|)

inline_for_extraction noextract
val transposewxw_uint32_f: #w:width -> n:nat{pow2 n == w} -> i:nat{i < n} -> ntuple (vec_t U32 w) w -> ntuple (vec_t U32 w) w
let transposewxw_uint32_f #w n i vs =
  let pow2i = normalize_term (pow2 i) in
  Lib.NTuple.createi w (transposewxw_uint32_f_l #w n i pow2i vs)


inline_for_extraction noextract
val transpose4x4_uint32: ntuple (vec_t U32 4) 4 -> ntuple (vec_t U32 4) 4
let transpose4x4_uint32 vs =
  let vs = transposewxw_uint32_f #4 2 0 vs in
  let vs = transposewxw_uint32_f #4 2 1 vs in
  (vs.(|0|), (vs.(|2|), (vs.(|1|), vs.(|3|))))

inline_for_extraction noextract
val transpose8x8_uint32: ntuple (vec_t U32 8) 8 -> ntuple (vec_t U32 8) 8
let transpose8x8_uint32 vs =
  let vs = transposewxw_uint32_f 3 0 vs in
  let vs = transposewxw_uint32_f 3 1 vs in
  let vs = transposewxw_uint32_f 3 2 vs in
  (vs.(|0|), (vs.(|2|), (vs.(|1|), (vs.(|3|), (vs.(|4|), (vs.(|6|), (vs.(|5|), vs.(|7|))))))))


inline_for_extraction noextract
val transpose16x16_uint32: ntuple (vec_t U32 16) 16 -> ntuple (vec_t U32 16) 16
let transpose16x16_uint32 vs =
  let vs = transposewxw_uint32_f 4 0 vs in
  let vs = transposewxw_uint32_f 4 1 vs in
  let vs = transposewxw_uint32_f 4 2 vs in
  let vs = transposewxw_uint32_f 4 3 vs in
  (vs.(|0|), (vs.(|2|), (vs.(|1|), (vs.(|3|), (vs.(|4|), (vs.(|6|), (vs.(|5|), (vs.(|7|),
    (vs.(|8|), (vs.(|10|), (vs.(|9|), (vs.(|11|), (vs.(|12|), (vs.(|14|), (vs.(|13|), vs.(|15|))))))))))))))))


#push-options "--initial_fuel 16 --max_fuel 16"
let transposewxw #t #w vs =
  match (t, w) with
  | (_, 1) -> vs
  | (U32, 4) -> transpose4x4_uint32 vs
  | (U32, 8) -> transpose8x8_uint32 vs
  | (U32, 16) -> transpose16x16_uint32 vs
  | _ -> admit()
#pop-options

let transposewxw_lemma #t #w vs = admit()
