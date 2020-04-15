module Hacl.Spec.Chacha20.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open Hacl.Spec.Chacha20.Vec

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

/// (vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16]

val transpose4_lemma: k:state 4 -> i:nat{i < 16 * 4} ->
  Lemma ((vec_v (transpose4 k).[i / 4]).[i % 4] == ((transpose_state k).[i / 16]).[i % 16])
let transpose4_lemma st i =
  // let (r0,(r1,(r2,r3))) = transposewxw #U32 #4 (st.[0],(st.[1],(st.[2],st.[3]))) in
  // transposewxw_lemma #U32 #4 (st.[0],(st.[1],(st.[2],st.[3])));
  // let (r4,(r5,(r6,r7))) = transposewxw #U32 #4 (st.[4],(st.[5],(st.[6],st.[7]))) in
  // transposewxw_lemma #U32 #4 (st.[4],(st.[5],(st.[6],st.[7])));
  // let (r8,(r9,(r10,r11))) = transposewxw #U32 #4 (st.[8],(st.[9],(st.[10],st.[11]))) in
  // transposewxw_lemma #U32 #4 (st.[8],(st.[9],(st.[10],st.[11])));
  // let (r12,(r13,(r14,r15))) = transposewxw #U32 #4 (st.[12],(st.[13],(st.[14],st.[15]))) in
  // transposewxw_lemma #U32 #4 (st.[12],(st.[13],(st.[14],st.[15])));
  admit()


val transpose8_lemma: k:state 8 -> i:nat{i < 16 * 8} ->
  Lemma ((vec_v (transpose8 k).[i / 8]).[i % 8] == ((transpose_state k).[i / 16]).[i % 16])
let transpose8_lemma st i =
  // let (v0,(v1,(v2,(v3,(v4,(v5,(v6,v7))))))) =
  //   transposewxw #U32 #8 (st.[0],(st.[1],(st.[2],(st.[3],(st.[4],(st.[5],(st.[6],st.[7]))))))) in
  // let (v8,(v9,(v10,(v11,(v12,(v13,(v14,v15))))))) =
  //   transposewxw #U32 #8 (st.[8],(st.[9],(st.[10],(st.[11],(st.[12],(st.[13],(st.[14],st.[15]))))))) in
  // transposewxw_lemma #U32 #8 (st.[0],(st.[1],(st.[2],(st.[3],(st.[4],(st.[5],(st.[6],st.[7])))))));
  // transposewxw_lemma #U32 #8 (st.[8],(st.[9],(st.[10],(st.[11],(st.[12],(st.[13],(st.[14],st.[15])))))));
  admit()

val transpose_lemma_index: #w:lanes -> k:state w -> i:nat{i < 16 * w} ->
  Lemma ((vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i
