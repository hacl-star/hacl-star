module Lib.IntVector.Transpose

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let vec_t2 (t:v_inttype) = vec_t t 2 & vec_t t 2

inline_for_extraction noextract
let vec_t4 (t:v_inttype) = vec_t t 4 & vec_t t 4 & vec_t t 4 & vec_t t 4

inline_for_extraction noextract
let vec_t8 (t:v_inttype) = vec_t t 8 & vec_t t 8 & vec_t t 8 & vec_t t 8 & vec_t t 8 & vec_t t 8 & vec_t t 8 & vec_t t 8

inline_for_extraction noextract
let vec_t16 (t:v_inttype) = vec_t t 16 & vec_t t 16 & vec_t t 16 & vec_t t 16 & vec_t t 16 & vec_t t 16 & vec_t t 16 & vec_t t 16


inline_for_extraction noextract
val transpose2x2: #t:v_inttype -> vec_t2 t -> vec_t2 t

inline_for_extraction noextract
val transpose4x4: #t:v_inttype{t = U32 \/ t = U64} -> vec_t4 t -> vec_t4 t

inline_for_extraction noextract
val transpose8x8: #t:v_inttype{t = U32 \/ t = U64} -> vec_t8 t -> vec_t8 t

inline_for_extraction noextract
val transpose16x16: #t:v_inttype{t = U32} -> vec_t16 t & vec_t16 t -> vec_t16 t & vec_t16 t


inline_for_extraction noextract
let transpose2x2_lseq (#t:v_inttype) (vs:lseq (vec_t t 2) 2) : lseq (vec_t t 2) 2 =
  let (v0,v1) = (vs.[0],vs.[1]) in
  let (r0,r1) = transpose2x2 (v0,v1) in
  create2 r0 r1

inline_for_extraction noextract
let transpose4x4_lseq (#t:v_inttype{t = U32 \/ t = U64}) (vs:lseq (vec_t t 4) 4) : lseq (vec_t t 4) 4 =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let (r0,r1,r2,r3) = transpose4x4 (v0,v1,v2,v3) in
  create4 r0 r1 r2 r3

inline_for_extraction noextract
let transpose8x8_lseq (#t:v_inttype{t = U32 \/ t = U64}) (vs:lseq (vec_t t 8) 8) : lseq (vec_t t 8) 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (r0,r1,r2,r3,r4,r5,r6,r7) = transpose8x8 (v0,v1,v2,v3,v4,v5,v6,v7) in
  create8 r0 r1 r2 r3 r4 r5 r6 r7

inline_for_extraction noextract
let transpose16x16_lseq (#t:v_inttype{t = U32}) (vs:lseq (vec_t t 16) 16) : lseq (vec_t t 16) 16 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (vs.[8],vs.[9],vs.[10],vs.[11],vs.[12],vs.[13],vs.[14],vs.[15]) in
  let ((r0,r1,r2,r3,r4,r5,r6,r7),(r8,r9,r10,r11,r12,r13,r14,r15)) =
    transpose16x16 ((v0,v1,v2,v3,v4,v5,v6,v7), (v8,v9,v10,v11,v12,v13,v14,v15)) in
  create16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15


val transpose2x2_lemma: #t:v_inttype -> vs:lseq (vec_t t 2) 2 ->
  Lemma (forall (i:nat{i < 2}) (j:nat{j < 2}). (vec_v (transpose2x2_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])

val transpose4x4_lemma: #t:v_inttype{t = U32 \/ t = U64} -> vs:lseq (vec_t t 4) 4 ->
  Lemma (forall (i:nat{i < 4}) (j:nat{j < 4}). (vec_v (transpose4x4_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])

val transpose8x8_lemma: #t:v_inttype{t = U32 \/ t = U64} -> vs:lseq (vec_t t 8) 8 ->
  Lemma (forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v (transpose8x8_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])

val transpose16x16_lemma: #t:v_inttype{t = U32} -> vs:lseq (vec_t t 16) 16 ->
  Lemma (forall (i:nat{i < 16}) (j:nat{j < 16}). (vec_v (transpose16x16_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])
