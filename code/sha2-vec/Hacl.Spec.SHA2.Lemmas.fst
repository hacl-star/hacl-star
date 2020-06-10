module Hacl.Spec.SHA2.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Spec.Hash.Definitions
open Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val transpose_ws2_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 2}
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    (vec_v (transpose_ws2 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws2_lemma_ij #a #m ws j i =
  let l = lanes a m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * l) l in
  eq_intro (sub (transpose_ws2 ws) (i_sub * l) l) (transpose2x2_lseq vs);
  assert ((vec_v (transpose_ws2 ws).[i]).[j] == (vec_v (transpose2x2_lseq vs).[j_sub]).[j]);
  transpose2x2_lemma vs;
  assert ((vec_v (transpose_ws2 ws).[i]).[j] == (vec_v ws.[i_sub * lanes a m + j]).[j_sub])


val transpose_ws4_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4} // lanes a m * lanes a m = 16
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    (vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws4_lemma_ij #a #m ws j i =
  let l = lanes a m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * l) l in
  eq_intro (sub (transpose_ws4 ws) (i_sub * l) l) (transpose4x4_lseq vs);
  //assert ((transpose_ws4 ws).[i] == (sub (transpose_ws4 ws) (i_sub * l) l).[j_sub]);
  //assert ((transpose_ws4 ws).[i] == (transpose4x4_lseq vs).[j_sub]);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v (transpose4x4_lseq vs).[j_sub]).[j]);
  transpose4x4_lemma vs;
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v vs.[j]).[j_sub]);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i_sub * l + j]).[j_sub])


val transpose_ws8_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 8}
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    (vec_v (transpose_ws8 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws8_lemma_ij #a #m ws j i =
  let l = lanes a m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * l) l in
  eq_intro (sub (transpose_ws8 ws) (i_sub * l) l) (transpose8x8_lseq vs);
  assert ((vec_v (transpose_ws8 ws).[i]).[j] == (vec_v (transpose8x8_lseq vs).[j_sub]).[j]);
  transpose8x8_lemma vs;
  assert ((vec_v (transpose_ws8 ws).[i]).[j] == (vec_v ws.[i_sub * lanes a m + j]).[j_sub])


val transpose_ws16_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 16}
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    (vec_v (transpose_ws16 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws16_lemma_ij #a #m ws j i =
  let l = lanes a m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * l) l in
  //eq_intro (sub (transpose_ws16 ws) (i_sub * l) l) (transpose16x16_lseq vs);
  assert ((vec_v (transpose_ws16 ws).[i]).[j] == (vec_v (transpose16x16_lseq vs).[j_sub]).[j]);
  transpose16x16_lemma vs;
  assert ((vec_v (transpose_ws16 ws).[i]).[j] == (vec_v ws.[i_sub * lanes a m + j]).[j_sub])


val transpose_ws_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    ((ws_spec_v (transpose_ws ws)).[j]).[i] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws_lemma_ij #a #m ws j i =
  assert (((ws_spec_v (transpose_ws ws)).[j]).[i] == (vec_v (transpose_ws ws).[i]).[j]);
  match lanes a m with
  | 1 -> ()
  | 2 -> transpose_ws2_lemma_ij #a #m ws j i
  | 4 -> transpose_ws4_lemma_ij #a #m ws j i
  | 8 -> transpose_ws8_lemma_ij #a #m ws j i
  | 16 -> transpose_ws16_lemma_ij #a #m ws j i


val transpose_state2_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 2}
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    Seq.index (vec_v (transpose_state st).[ind / l]) (ind % l) ==
    Seq.index (state_spec_v st).[j] (i / word_length a))

let transpose_state2_lemma #a #m st j i =
  let r0 = transpose2x2_lseq (sub st 0 2) in
  transpose2x2_lemma (sub st 0 2);
  let r1 = transpose2x2_lseq (sub st 2 2) in
  transpose2x2_lemma (sub st 2 2);
  let r3 = transpose2x2_lseq (sub st 4 2) in
  transpose2x2_lemma (sub st 4 2);
  let r4 = transpose2x2_lseq (sub st 6 2) in
  transpose2x2_lemma (sub st 6 2)


val transpose_state4_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4}
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    Seq.index (vec_v (transpose_state st).[ind / l]) (ind % l) ==
    Seq.index (state_spec_v st).[j] (i / word_length a))

let transpose_state4_lemma #a #m st j i =
  let r0 = transpose4x4_lseq (sub st 0 4) in
  transpose4x4_lemma (sub st 0 4);
  let r1 = transpose4x4_lseq (sub st 4 4) in
  transpose4x4_lemma (sub st 4 4)


val transpose_state8_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 8}
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    Seq.index (vec_v (transpose_state8 st).[ind / l]) (ind % l) ==
    Seq.index (state_spec_v st).[j] (i / word_length a))

let transpose_state8_lemma #a #m st j i =
  let l = lanes a m in
  let ind = 8 * j + i / word_length a in
  let r0 = transpose8x8_lseq st in
  transpose8x8_lemma st


val transpose_state16_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 16}
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    Seq.index (vec_v (transpose_state16 st).[ind / l]) (ind % l) ==
    Seq.index (state_spec_v st).[j] (i / word_length a))

let transpose_state16_lemma #a #m st j i =
  let st16 = create 16 (zero_element a m) in
  let st16 = update_sub st16 0 8 st in
  let st_r = transpose16x16_lseq st16 in
  transpose16x16_lemma st16;
  assert (forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v st_r.[i]).[j] == (vec_v st.[j]).[i]);
  let (st0,st1,st2,st3,st4,st5,st6,st7) = (st_r.[0],st_r.[1],st_r.[2],st_r.[3],st_r.[4],st_r.[5],st_r.[6],st_r.[7]) in
  let (st8,st9,st10,st11,st12,st13,st14,st15) = (st_r.[8],st_r.[9],st_r.[10],st_r.[11],st_r.[12],st_r.[13],st_r.[14],st_r.[15]) in
  let st0' = vec_interleave_low_n 8 st0 st1 in
  vec_interleave_low_n_lemma_uint32_16_8 st0 st1;
  let st1' = vec_interleave_low_n 8 st2 st3 in
  vec_interleave_low_n_lemma_uint32_16_8 st2 st3;
  let st2' = vec_interleave_low_n 8 st4 st5 in
  vec_interleave_low_n_lemma_uint32_16_8 st4 st5;
  let st3' = vec_interleave_low_n 8 st6 st7 in
  vec_interleave_low_n_lemma_uint32_16_8 st6 st7;
  let st4' = vec_interleave_low_n 8 st8 st9 in
  vec_interleave_low_n_lemma_uint32_16_8 st8 st9;
  let st5' = vec_interleave_low_n 8 st10 st11 in
  vec_interleave_low_n_lemma_uint32_16_8 st10 st11;
  let st6' = vec_interleave_low_n 8 st12 st13 in
  vec_interleave_low_n_lemma_uint32_16_8 st12 st13;
  let st7' = vec_interleave_low_n 8 st14 st15 in
  vec_interleave_low_n_lemma_uint32_16_8 st14 st15


val transpose_state_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    (Seq.index (vec_v (transpose_state st).[ind / l])) (ind % l) ==
    (Seq.index (state_spec_v st).[j] (i / word_length a)))

let transpose_state_lemma_ij #a #m st j i =
  match lanes a m with
  | 1 -> ()
  | 2 -> transpose_state2_lemma #a #m st j i
  | 4 -> transpose_state4_lemma #a #m st j i
  | 8 -> transpose_state8_lemma #a #m st j i
  | 16 -> transpose_state16_lemma #a #m st j i
