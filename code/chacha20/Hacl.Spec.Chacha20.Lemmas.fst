module Hacl.Spec.Chacha20.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector

open Hacl.Spec.Chacha20.Vec


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

/// (vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16]


unfold
let op_Array_Access (#w:lanes) (a:uint32xN w) i = (vec_v a).[i]


noextract
let transpose4x4 (vs:lseq (uint32xN 4) 4) : lseq (uint32xN 4) 4 =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let (v0'',v1'',v2'',v3'') = transpose4x4 (v0,v1,v2,v3) in
  create4 v0'' v1'' v2'' v3''


val transpose4x4_lemma_ij: vs:lseq (uint32xN 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4 vs).[i]).[j] == (vec_v vs.[j]).[i])
let transpose4x4_lemma_ij vs i j =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let v0' = vec_interleave_low v0 v1 in
  vec_interleave_low_lemma_uint32_4 v0 v1;
  let v1' = vec_interleave_high v0 v1 in
  vec_interleave_high_lemma_uint32_4 v0 v1;
  let v2' = vec_interleave_low v2 v3 in
  vec_interleave_low_lemma_uint32_4 v2 v3;
  let v3' = vec_interleave_high v2 v3 in
  vec_interleave_high_lemma_uint32_4 v2 v3;
  let v0'' = vec_interleave_low_n 2 v0' v2' in
  vec_interleave_low_n_lemma_uint32_4_2 v0' v2';
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  vec_interleave_high_n_lemma_uint32_4_2 v0' v2';
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  vec_interleave_low_n_lemma_uint32_4_2 v1' v3';
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  vec_interleave_high_n_lemma_uint32_4_2 v1' v3';
  let res = create4 v0'' v1'' v2'' v3'' in
  ()


val transpose4x4_lemma: vs:lseq (uint32xN 4) 4 ->
  Lemma ((forall (i:nat{i < 4}) (j:nat{j < 4}). (vec_v (transpose4x4 vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose4x4_lemma vs =
  Classical.forall_intro_2 (transpose4x4_lemma_ij vs)


val transpose4_lemma:
    k:state 4
  -> i:nat{i < 16 * 4} ->
  Lemma ((vec_v (transpose4 k).[i / 4]).[i % 4] == ((transpose_state k).[i / 16]).[i % 16])
let transpose4_lemma st i =
  let r0 = transpose4x4 (sub st 0 4) in
  transpose4x4_lemma (sub st 0 4);
  let r1 = transpose4x4 (sub st 4 4) in
  transpose4x4_lemma (sub st 4 4);
  let r2 = transpose4x4 (sub st 8 4) in
  transpose4x4_lemma (sub st 8 4);
  let r3 = transpose4x4 (sub st 12 4) in
  transpose4x4_lemma (sub st 12 4);
  let (v0,v1,v2,v3)     = (r0.[0], r0.[1], r0.[2], r0.[3]) in
  let (v4,v5,v6,v7)     = (r1.[0], r1.[1], r1.[2], r1.[3]) in
  let (v8,v9,v10,v11)   = (r2.[0], r2.[1], r2.[2], r2.[3]) in
  let (v12,v13,v14,v15) = (r3.[0], r3.[1], r3.[2], r3.[3]) in
  let res : lseq (uint32xN 4) 16 = create16 v0 v4 v8 v12 v1 v5 v9 v13 v2 v6 v10 v14 v3 v7 v11 v15 in
  ()


noextract
let transpose8x8 (vs:lseq (uint32xN 8) 8) : lseq (uint32xN 8) 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (v0''', v2''', v4''', v6''', v1''', v3''', v5''', v7''') = transpose8x8 (v0,v1,v2,v3,v4,v5,v6,v7) in
  create8 v0''' v2''' v4''' v6''' v1''' v3''' v5''' v7'''


val transpose8x8_lemma_ij: vs:lseq (uint32xN 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma ((vec_v (transpose8x8 vs).[i]).[j] == (vec_v vs.[j]).[i])
let transpose8x8_lemma_ij vs i j =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let v0' = vec_interleave_low v0 v1 in
  vec_interleave_low_lemma_uint32_8 v0 v1;
  let r0: lseq uint32 8 = create8 v0.(0) v1.(0) v0.(1) v1.(1) v0.(4) v1.(4) v0.(5) v1.(5) in
  assert (vec_v v0' == r0);
  let v1' = vec_interleave_high v0 v1 in
  vec_interleave_high_lemma_uint32_8 v0 v1;
  let r1: lseq uint32 8 = create8 v0.(2) v1.(2) v0.(3) v1.(3) v0.(6) v1.(6) v0.(7) v1.(7) in
  assert (vec_v v1' == r1);
  let v2' = vec_interleave_low v2 v3 in
  vec_interleave_low_lemma_uint32_8 v2 v3;
  let r2: lseq uint32 8 = create8 v2.(0) v3.(0) v2.(1) v3.(1) v2.(4) v3.(4) v2.(5) v3.(5) in
  assert (vec_v v2' == r2);
  let v3' = vec_interleave_high v2 v3 in
  vec_interleave_high_lemma_uint32_8 v2 v3;
  let r3: lseq uint32 8 = create8 v2.(2) v3.(2) v2.(3) v3.(3) v2.(6) v3.(6) v2.(7) v3.(7) in
  assert (vec_v v3' == r3);
  let v4' = vec_interleave_low v4 v5 in
  vec_interleave_low_lemma_uint32_8 v4 v5;
  let r4: lseq uint32 8 = create8 v4.(0) v5.(0) v4.(1) v5.(1) v4.(4) v5.(4) v4.(5) v5.(5) in
  assert (vec_v v4' == r4);
  let v5' = vec_interleave_high v4 v5 in
  vec_interleave_high_lemma_uint32_8 v4 v5;
  let r5: lseq uint32 8 = create8 v4.(2) v5.(2) v4.(3) v5.(3) v4.(6) v5.(6) v4.(7) v5.(7) in
  assert (vec_v v5' == r5);
  let v6' = vec_interleave_low v6 v7 in
  vec_interleave_low_lemma_uint32_8 v6 v7;
  let r6: lseq uint32 8 = create8 v6.(0) v7.(0) v6.(1) v7.(1) v6.(4) v7.(4) v6.(5) v7.(5) in
  assert (vec_v v6' == r6);
  let v7' = vec_interleave_high v6 v7 in
  vec_interleave_high_lemma_uint32_8 v6 v7;
  let r7: lseq uint32 8 = create8 v6.(2) v7.(2) v6.(3) v7.(3) v6.(6) v7.(6) v6.(7) v7.(7) in
  assert (vec_v v7' == r7);

  let v0'' = vec_interleave_low_n 4 v0' v2' in
  vec_interleave_low_n_lemma_uint32_8_4 v0' v2';
  let r0': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v0.(4) v1.(4) v2.(4) v3.(4) in
  assert (vec_v v0'' == r0');

  let v1'' = vec_interleave_high_n 4 v0' v2' in
  vec_interleave_high_n_lemma_uint32_8_4 v0' v2';
  let r1': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v0.(5) v1.(5) v2.(5) v3.(5) in
  assert (vec_v v1'' == r1');

  let v2'' = vec_interleave_low_n 4 v1' v3' in
  vec_interleave_low_n_lemma_uint32_8_4 v1' v3';
  let r2': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v0.(6) v1.(6) v2.(6) v3.(6) in
  assert (vec_v v2'' == r2');

  let v3'' = vec_interleave_high_n 4 v1' v3' in
  vec_interleave_high_n_lemma_uint32_8_4 v1' v3';
  let r3': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v0.(7) v1.(7) v2.(7) v3.(7) in
  assert (vec_v v3'' == r3');

  let v4'' = vec_interleave_low_n 4 v4' v6' in
  vec_interleave_low_n_lemma_uint32_8_4 v4' v6';
  let r4': lseq uint32 8 = create8 v4.(0) v5.(0) v6.(0) v7.(0) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v4'' == r4');

  let v5'' = vec_interleave_high_n 4 v4' v6' in
  vec_interleave_high_n_lemma_uint32_8_4 v4' v6';
  let r5': lseq uint32 8 = create8 v4.(1) v5.(1) v6.(1) v7.(1) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v5'' == r5');

  let v6'' = vec_interleave_low_n 4 v5' v7' in
  vec_interleave_low_n_lemma_uint32_8_4 v5' v7';
  let r6': lseq uint32 8 = create8 v4.(2) v5.(2) v6.(2) v7.(2) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v6'' == r6');

  let v7'' = vec_interleave_high_n 4 v5' v7' in
  vec_interleave_high_n_lemma_uint32_8_4 v5' v7';
  let r7': lseq uint32 8 = create8 v4.(3) v5.(3) v6.(3) v7.(3) v4.(7) v5.(7) v6.(7) v7.(7) in
  assert (vec_v v7'' == r7');

  let v0''' = vec_interleave_low_n 2 v0'' v4'' in
  vec_interleave_low_n_lemma_uint32_8_2 v0'' v4'';
  let r0'': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v4.(0) v5.(0) v6.(0) v7.(0) in
  assert (vec_v v0''' == r0'');

  let v1''' = vec_interleave_high_n 2 v0'' v4'' in
  vec_interleave_high_n_lemma_uint32_8_2 v0'' v4'';
  let r1'': lseq uint32 8 = create8 v0.(4) v1.(4) v2.(4) v3.(4) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v1''' == r1'');

  let v2''' = vec_interleave_low_n 2 v1'' v5'' in
  vec_interleave_low_n_lemma_uint32_8_2 v1'' v5'';
  let r2'': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v4.(1) v5.(1) v6.(1) v7.(1) in
  assert (vec_v v2''' == r2'');

  let v3''' = vec_interleave_high_n 2 v1'' v5'' in
  vec_interleave_high_n_lemma_uint32_8_2 v1'' v5'';
  let r3'': lseq uint32 8 = create8 v0.(5) v1.(5) v2.(5) v3.(5) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v3''' == r3'');

  let v4''' = vec_interleave_low_n 2 v2'' v6'' in
  vec_interleave_low_n_lemma_uint32_8_2 v2'' v6'';
  let r4'': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v4.(2) v5.(2) v6.(2) v7.(2) in
  assert (vec_v v4''' == r4'');

  let v5''' = vec_interleave_high_n 2 v2'' v6'' in
  vec_interleave_high_n_lemma_uint32_8_2 v2'' v6'';
  let r5'': lseq uint32 8 = create8 v0.(6) v1.(6) v2.(6) v3.(6) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v5''' == r5'');

  let v6''' = vec_interleave_low_n 2 v3'' v7'' in
  vec_interleave_low_n_lemma_uint32_8_2 v3'' v7'';
  let r6'': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v4.(3) v5.(3) v6.(3) v7.(3) in
  assert (vec_v v6''' == r6'');

  let v7''' = vec_interleave_high_n 2 v3'' v7'' in
  vec_interleave_high_n_lemma_uint32_8_2 v3'' v7'';
  let r7'': lseq uint32 8 = create8 v0.(7) v1.(7) v2.(7) v3.(7) v4.(7) v5.(7) v6.(7) v7.(7) in
  assert (vec_v v7''' == r7'');
  let res = create8 v0''' v2''' v4''' v6''' v1''' v3''' v5''' v7''' in
  ()


val transpose8x8_lemma: vs:lseq (uint32xN 8) 8 ->
  Lemma ((forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v (transpose8x8 vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose8x8_lemma vs =
  Classical.forall_intro_2 (transpose8x8_lemma_ij vs)


val transpose8_lemma:
    k:state 8
  -> i:nat{i < 16 * 8} ->
  Lemma ((vec_v (transpose8 k).[i / 8]).[i % 8] == ((transpose_state k).[i / 16]).[i % 16])
let transpose8_lemma st i =
  let r0 = transpose8x8 (sub st 0 8) in
  transpose8x8_lemma (sub st 0 8);
  let r1 = transpose8x8 (sub st 8 8) in
  transpose8x8_lemma (sub st 8 8);
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (r0.[0],r0.[1],r0.[2],r0.[3],r0.[4],r0.[5],r0.[6],r0.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (r1.[0],r1.[1],r1.[2],r1.[3],r1.[4],r1.[5],r1.[6],r1.[7]) in
  let res : lseq (uint32xN 8) 16 = create16 v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15 in
  ()


val transpose_lemma_index:
    #w:lanes
  -> k:state w
  -> i:nat{i < 16 * w} ->
  Lemma ((vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i
