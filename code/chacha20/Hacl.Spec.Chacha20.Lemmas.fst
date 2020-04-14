module Hacl.Spec.Chacha20.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Hacl.Spec.Chacha20.Vec

#set-options "--z3rlimit 50 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

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
  let r0 = transpose8x8_lseq (sub st 0 8) in
  transpose8x8_lemma (sub st 0 8);
  let r1 = transpose8x8_lseq (sub st 8 8) in
  transpose8x8_lemma (sub st 8 8);
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (r0.[0],r0.[1],r0.[2],r0.[3],r0.[4],r0.[5],r0.[6],r0.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (r1.[0],r1.[1],r1.[2],r1.[3],r1.[4],r1.[5],r1.[6],r1.[7]) in
  let res : lseq (uint32xN 8) 16 = create16 v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15 in
  ()


val transpose_lemma_index: #w:lanes -> k:state w -> i:nat{i < 16 * w} ->
  Lemma ((vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i
