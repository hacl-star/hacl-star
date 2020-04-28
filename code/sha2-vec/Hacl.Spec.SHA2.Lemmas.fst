module Hacl.Spec.SHA2.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Spec.Hash.Definitions
open Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

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
  | 4 -> transpose_ws4_lemma_ij #a #m ws j i
  | 8 -> transpose_ws8_lemma_ij #a #m ws j i
  | _ -> admit()


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
  | 4 -> transpose_state4_lemma #a #m st j i
  | 8 -> transpose_state8_lemma #a #m st j i
  | _ -> admit()
