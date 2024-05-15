module Hacl.Spec.SHA3.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

val transpose_ws4_lemma_ij:
  #m:m_spec{m == M256} // lanes m * lanes m = 32
  -> ws:ws_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma
   (let l = lanes m in
    (vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws4_lemma_ij #m ws j i =
  let l = lanes m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * l) l in
  eq_intro (sub (transpose_ws4 ws) (i_sub * l) l) (transpose4x4_lseq vs);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v (transpose4x4_lseq vs).[j_sub]).[j]);
  transpose4x4_lemma vs;
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v vs.[j]).[j_sub]);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i_sub * l + j]).[j_sub])

val transpose_ws_lemma_ij:
    #m:m_spec
  -> ws:ws_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma
   (let l = lanes m in
    ((ws_spec_v #m (transpose_ws ws)).[j]).[i] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws_lemma_ij #m ws j i =
  assert (((ws_spec_v #m (transpose_ws ws)).[j]).[i] == (vec_v (transpose_ws ws).[i]).[j]);
  match m with
  | M32 -> ()
  | M256 -> transpose_ws4_lemma_ij #m ws j i

val transpose_s4_lemma:
    #m:m_spec{lanes m == 4}
  -> ws:ws_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32 * 8} ->
  Lemma
   (let l = lanes m in
    let ind = 32 * j + i / 8 in
    Seq.index (vec_v (transpose_s_ws ws).[ind / l]) (ind % l) ==
    Seq.index (ws_spec_v ws).[j] (i / 8))

let transpose_s4_lemma #m ws _ _ =
  let r0 = transpose4x4_lseq (sub ws 0 4) in
  transpose4x4_lemma (sub ws 0 4);
  let r1 = transpose4x4_lseq (sub ws 4 4) in
  transpose4x4_lemma (sub ws 4 4);
  let r2 = transpose4x4_lseq (sub ws 8 4) in
  transpose4x4_lemma (sub ws 8 4);
  let r3 = transpose4x4_lseq (sub ws 12 4) in
  transpose4x4_lemma (sub ws 12 4);
  let r4 = transpose4x4_lseq (sub ws 16 4) in
  transpose4x4_lemma (sub ws 16 4);
  let r5 = transpose4x4_lseq (sub ws 20 4) in
  transpose4x4_lemma (sub ws 20 4);
  let r6 = transpose4x4_lseq (sub ws 24 4) in
  transpose4x4_lemma (sub ws 24 4);
  let r7 = transpose4x4_lseq (sub ws 28 4) in
  transpose4x4_lemma (sub ws 28 4)

val transpose_s_lemma_ij:
    #m:m_spec
  -> ws:ws_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32 * 8} ->
  Lemma
   (let l = lanes m in
    let ind = 32 * j + i / 8 in
    Seq.index (vec_v (transpose_s_ws ws).[ind / l]) (ind % l) ==
    Seq.index (ws_spec_v ws).[j] (i / 8))

let transpose_s_lemma_ij #m ws j i =
  match m with
  | M32 -> ()
  | M256 -> transpose_s4_lemma #m ws j i
