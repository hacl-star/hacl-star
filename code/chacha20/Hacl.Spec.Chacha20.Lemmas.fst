module Hacl.Spec.Chacha20.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Hacl.Spec.Chacha20.Vec

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

/// (vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16]

val transpose4_lemma: k:state 4 -> i:nat{i < 16 * 4} ->
  Lemma ((vec_v (transpose4 k).[i / 4]).[i % 4] == ((transpose_state k).[i / 16]).[i % 16])
let transpose4_lemma st i =
  let r0 = transpose4x4_lseq (sub st 0 4) in
  transpose4x4_lemma (sub st 0 4);
  let r1 = transpose4x4_lseq (sub st 4 4) in
  transpose4x4_lemma (sub st 4 4);
  let r2 = transpose4x4_lseq (sub st 8 4) in
  transpose4x4_lemma (sub st 8 4);
  let r3 = transpose4x4_lseq (sub st 12 4) in
  transpose4x4_lemma (sub st 12 4)


val transpose8_lemma: k:state 8 -> i:nat{i < 16 * 8} ->
  Lemma ((vec_v (transpose8 k).[i / 8]).[i % 8] == ((transpose_state k).[i / 16]).[i % 16])
let transpose8_lemma st i =
  let r0 = transpose8x8_lseq (sub st 0 8) in
  transpose8x8_lemma (sub st 0 8);
  let r1 = transpose8x8_lseq (sub st 8 8) in
  transpose8x8_lemma (sub st 8 8)


val transpose_lemma_index: #w:lanes -> k:state w -> i:nat{i < 16 * w} ->
  Lemma ((vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i
