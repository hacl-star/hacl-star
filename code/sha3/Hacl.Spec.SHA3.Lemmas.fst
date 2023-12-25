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
  #m:m_spec{lanes m == 4} // lanes m * lanes m = 32
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
    #m:m_spec{is_supported m}
  -> ws:ws_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma
   (let l = lanes m in
    ((ws_spec_v #m (transpose_ws ws)).[j]).[i] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws_lemma_ij #m ws j i =
  assert (((ws_spec_v #m (transpose_ws ws)).[j]).[i] == (vec_v (transpose_ws ws).[i]).[j]);
  match lanes m with
  | 1 -> ()
  | 4 -> transpose_ws4_lemma_ij #m ws j i
