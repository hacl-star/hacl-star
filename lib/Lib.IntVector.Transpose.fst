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

// inline_for_extraction noextract
// val transposewxw_uint32_f: #w:width -> n:nat{pow2 n == w} -> i:nat{i < n} -> ntuple (vec_t U32 w) w -> ntuple (vec_t U32 w) w
// let transposewxw_uint32_f #w n i vs =
//   let pow2i = normalize_term (pow2 i) in
//   Lib.NTuple.createi w (transposewxw_uint32_f_l #w n i pow2i vs)

inline_for_extraction noextract
val transpose4x4_uint32: ntuple (vec_t U32 4) 4 -> ntuple (vec_t U32 4) 4
let transpose4x4_uint32 (vs0,(vs1,(vs2,vs3))) =
  let (vs0,(vs1,(vs2,vs3))) = Lib.NTuple.createi 4 (transposewxw_uint32_f_l #4 2 0 1 (vs0,(vs1,(vs2,vs3)))) in
  let (vs0,(vs1,(vs2,vs3))) = Lib.NTuple.createi 4 (transposewxw_uint32_f_l #4 2 1 2 (vs0,(vs1,(vs2,vs3)))) in
  (vs0,(vs2,(vs1,vs3)))

inline_for_extraction noextract
val transpose8x8_uint32: ntuple (vec_t U32 8) 8 -> ntuple (vec_t U32 8) 8
let transpose8x8_uint32 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7))))))) =
  let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7))))))) =
    Lib.NTuple.createi 8 (transposewxw_uint32_f_l #8 3 0 1 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7)))))))) in
  let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7))))))) =
    Lib.NTuple.createi 8 (transposewxw_uint32_f_l #8 3 1 2 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7)))))))) in
  let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7))))))) =
    Lib.NTuple.createi 8 (transposewxw_uint32_f_l #8 3 2 4 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7)))))))) in
  (vs0,(vs2,(vs1,(vs3,(vs4,(vs6,(vs5,vs7)))))))

inline_for_extraction noextract
val transpose16x16_uint32: ntuple (vec_t U32 16) 16 -> ntuple (vec_t U32 16) 16
let transpose16x16_uint32 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) = admit()
  // let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) =
  //   Lib.NTuple.createi 16 (transposewxw_uint32_f_l #16 4 0 1 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15)))))))))))))))) in

  // let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) =
  //   Lib.NTuple.createi 16 (transposewxw_uint32_f_l #16 4 1 2 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15)))))))))))))))) in

  // let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) =
  //   Lib.NTuple.createi 16 (transposewxw_uint32_f_l #16 4 2 4 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15)))))))))))))))) in

  // let (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) =
  //   Lib.NTuple.createi 16 (transposewxw_uint32_f_l #16 4 3 8 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15)))))))))))))))) in

  // (vs0,(vs2,(vs1,(vs3,(vs4,(vs6,(vs5,(vs7,(vs8,(vs10,(vs9,(vs11,(vs12,(vs14,(vs13,vs15)))))))))))))))


let transpose4x4 #t (vs0,(vs1,(vs2,vs3))) =
  match t with
  | U32 -> transpose4x4_uint32 (vs0,(vs1,(vs2,vs3)))
  | _ -> admit()

let transpose8x8 #t (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7))))))) =
  match t with
  | U32 -> transpose8x8_uint32 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,vs7)))))))
  | _ -> admit()

let transpose16x16 #t (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15))))))))))))))) =
  match t with
  | U32 -> transpose16x16_uint32 (vs0,(vs1,(vs2,(vs3,(vs4,(vs5,(vs6,(vs7,(vs8,(vs9,(vs10,(vs11,(vs12,(vs13,(vs14,vs15)))))))))))))))
  | _ -> admit()


let transpose4x4_lemma #t vs = admit()
let transpose8x8_lemma #t vs = admit()
let transpose16x16_lemma #t vs = admit()
