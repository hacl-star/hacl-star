module Lib.IntVector.Transpose

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract
val transpose4x4_uint32: #t:v_inttype{t == U32} -> vec_t4 t -> vec_t4 t
let transpose4x4_uint32 #t vs =
  let (v0,v1,v2,v3) = vs in
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  (v0'',v1'',v2'',v3'')


let transpose4x4 #t vs =
  match t with
  | U32 -> transpose4x4_uint32 #t vs
  | _ -> admit()


inline_for_extraction noextract
val transpose8x8_uint32: #t:v_inttype{t == U32} -> vec_t8 t -> vec_t8 t
let transpose8x8_uint32 #t vs =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = vs in
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  let v4'' = vec_interleave_low_n 2 v4' v6' in
  let v5'' = vec_interleave_high_n 2 v4' v6' in
  let v6'' = vec_interleave_low_n 2 v5' v7' in
  let v7'' = vec_interleave_high_n 2 v5' v7' in

  let v0''' = vec_interleave_low_n 4 v0'' v4'' in
  let v1''' = vec_interleave_high_n 4 v0'' v4'' in
  let v2''' = vec_interleave_low_n 4 v1'' v5'' in
  let v3''' = vec_interleave_high_n 4 v1'' v5'' in
  let v4''' = vec_interleave_low_n 4 v2'' v6'' in
  let v5''' = vec_interleave_high_n 4 v2'' v6'' in
  let v6''' = vec_interleave_low_n 4 v3'' v7'' in
  let v7''' = vec_interleave_high_n 4 v3'' v7'' in
  (v0''',v2''',v4''',v6''',v1''',v3''',v5''',v7''')


let transpose8x8 #t vs =
  match t with
  | U32 -> transpose8x8_uint32 #t vs
  | _ -> admit()


val transpose16x16_uint32_lseq: #t:v_inttype{t == U32} -> vs:lseq (vec_t t 16) 16 -> lseq (vec_t t 16) 16
let transpose16x16_uint32_lseq #t vs =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (vs.[8],vs.[9],vs.[10],vs.[11],vs.[12],vs.[13],vs.[14],vs.[15]) in

  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in
  let v8' = vec_interleave_low v8 v9 in
  let v9' = vec_interleave_high v8 v9 in
  let v10' = vec_interleave_low v10 v11 in
  let v11' = vec_interleave_high v10 v11 in
  let v12' = vec_interleave_low v12 v13 in
  let v13' = vec_interleave_high v12 v13 in
  let v14' = vec_interleave_low v14 v15 in
  let v15' = vec_interleave_high v14 v15 in

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v2'' = vec_interleave_high_n 2 v0' v2' in
  let v1'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  let v4'' = vec_interleave_low_n 2 v4' v6' in
  let v6'' = vec_interleave_high_n 2 v4' v6' in
  let v5'' = vec_interleave_low_n 2 v5' v7' in
  let v7'' = vec_interleave_high_n 2 v5' v7' in
  let v8'' = vec_interleave_low_n 2 v8' v10' in
  let v10'' = vec_interleave_high_n 2 v8' v10' in
  let v9'' = vec_interleave_low_n 2 v9' v11' in
  let v11'' = vec_interleave_high_n 2 v9' v11' in
  let v12'' = vec_interleave_low_n 2 v12' v14' in
  let v14'' = vec_interleave_high_n 2 v12' v14' in
  let v13'' = vec_interleave_low_n 2 v13' v15' in
  let v15'' = vec_interleave_high_n 2 v13' v15' in

  let v0' = vec_interleave_low_n 4 v0'' v4'' in
  let v4' = vec_interleave_high_n 4 v0'' v4'' in
  let v1' = vec_interleave_low_n 4 v1'' v5'' in
  let v5' = vec_interleave_high_n 4 v1'' v5'' in
  let v2' = vec_interleave_low_n 4 v2'' v6'' in
  let v6' = vec_interleave_high_n 4 v2'' v6'' in
  let v3' = vec_interleave_low_n 4 v3'' v7'' in
  let v7' = vec_interleave_high_n 4 v3'' v7'' in
  let v8' = vec_interleave_low_n 4 v8'' v12'' in
  let v12' = vec_interleave_high_n 4 v8'' v12'' in
  let v9' = vec_interleave_low_n 4 v9'' v13'' in
  let v13' = vec_interleave_high_n 4 v9'' v13'' in
  let v10' = vec_interleave_low_n 4 v10'' v14'' in
  let v14' = vec_interleave_high_n 4 v10'' v14'' in

  let v0 = vec_interleave_low_n 8 v0' v8' in
  let v8 = vec_interleave_high_n 8 v0' v8' in
  let v1 = vec_interleave_low_n 8 v1' v9' in
  let v9 = vec_interleave_high_n 8 v1' v9' in
  let v2 = vec_interleave_low_n 8 v2' v10' in
  let v10 = vec_interleave_high_n 8 v2' v10' in
  let v3 = vec_interleave_low_n 8 v3' v11' in
  let v11 = vec_interleave_high_n 8 v3' v11' in
  let v4 = vec_interleave_low_n 8 v4' v12' in
  let v12 = vec_interleave_high_n 8 v4' v12' in
  let v5 = vec_interleave_low_n 8 v5' v13' in
  let v13 = vec_interleave_high_n 8 v5' v13' in
  let v6 = vec_interleave_low_n 8 v6' v14' in
  let v14 = vec_interleave_high_n 8 v6' v14' in
  let v7 = vec_interleave_low_n 8 v7' v15' in
  let v15 = vec_interleave_high_n 8 v7' v15' in

  create16 v0 v2 v1 v3 v4 v6 v5 v7 v8 v10 v9 v11 v12 v14 v13 v15


let transpose16x16_lseq #t vs =
  match t with
  | U32 -> transpose16x16_uint32_lseq #t vs
  | _ -> admit()



val transpose4x4_uint32_lemma_ij: #t:v_inttype{t == U32}
  -> vs:lseq (vec_t t 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma ((vec_v (transpose4x4_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose4x4_uint32_lemma_ij #t vs i j =
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


let transpose4x4_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose4x4_uint32_lemma_ij vs)
  | _ -> admit()


unfold
let op_Array_Access (#t:v_inttype) (#w:width) (a:vec_t t w) i = (vec_v a).[i]


val transpose8x8_uint32_lemma_ij: #t:v_inttype{t == U32}
  -> vs:lseq (vec_t t 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma ((vec_v (transpose8x8_lseq vs).[i]).[j] == (vec_v vs.[j]).[i])

let transpose8x8_uint32_lemma_ij #t vs i j =
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

  let v0'' = vec_interleave_low_n 2 v0' v2' in
  vec_interleave_low_n_lemma_uint32_8_2 v0' v2';
  let r0': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v0.(4) v1.(4) v2.(4) v3.(4) in
  assert (vec_v v0'' == r0');

  let v1'' = vec_interleave_high_n 2 v0' v2' in
  vec_interleave_high_n_lemma_uint32_8_2 v0' v2';
  let r1': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v0.(5) v1.(5) v2.(5) v3.(5) in
  assert (vec_v v1'' == r1');

  let v2'' = vec_interleave_low_n 2 v1' v3' in
  vec_interleave_low_n_lemma_uint32_8_2 v1' v3';
  let r2': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v0.(6) v1.(6) v2.(6) v3.(6) in
  assert (vec_v v2'' == r2');

  let v3'' = vec_interleave_high_n 2 v1' v3' in
  vec_interleave_high_n_lemma_uint32_8_2 v1' v3';
  let r3': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v0.(7) v1.(7) v2.(7) v3.(7) in
  assert (vec_v v3'' == r3');

  let v4'' = vec_interleave_low_n 2 v4' v6' in
  vec_interleave_low_n_lemma_uint32_8_2 v4' v6';
  let r4': lseq uint32 8 = create8 v4.(0) v5.(0) v6.(0) v7.(0) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v4'' == r4');

  let v5'' = vec_interleave_high_n 2 v4' v6' in
  vec_interleave_high_n_lemma_uint32_8_2 v4' v6';
  let r5': lseq uint32 8 = create8 v4.(1) v5.(1) v6.(1) v7.(1) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v5'' == r5');

  let v6'' = vec_interleave_low_n 2 v5' v7' in
  vec_interleave_low_n_lemma_uint32_8_2 v5' v7';
  let r6': lseq uint32 8 = create8 v4.(2) v5.(2) v6.(2) v7.(2) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v6'' == r6');

  let v7'' = vec_interleave_high_n 2 v5' v7' in
  vec_interleave_high_n_lemma_uint32_8_2 v5' v7';
  let r7': lseq uint32 8 = create8 v4.(3) v5.(3) v6.(3) v7.(3) v4.(7) v5.(7) v6.(7) v7.(7) in
  assert (vec_v v7'' == r7');

  let v0''' = vec_interleave_low_n 4 v0'' v4'' in
  vec_interleave_low_n_lemma_uint32_8_4 v0'' v4'';
  let r0'': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v4.(0) v5.(0) v6.(0) v7.(0) in
  assert (vec_v v0''' == r0'');

  let v1''' = vec_interleave_high_n 4 v0'' v4'' in
  vec_interleave_high_n_lemma_uint32_8_4 v0'' v4'';
  let r1'': lseq uint32 8 = create8 v0.(4) v1.(4) v2.(4) v3.(4) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v1''' == r1'');

  let v2''' = vec_interleave_low_n 4 v1'' v5'' in
  vec_interleave_low_n_lemma_uint32_8_4 v1'' v5'';
  let r2'': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v4.(1) v5.(1) v6.(1) v7.(1) in
  assert (vec_v v2''' == r2'');

  let v3''' = vec_interleave_high_n 4 v1'' v5'' in
  vec_interleave_high_n_lemma_uint32_8_4 v1'' v5'';
  let r3'': lseq uint32 8 = create8 v0.(5) v1.(5) v2.(5) v3.(5) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v3''' == r3'');

  let v4''' = vec_interleave_low_n 4 v2'' v6'' in
  vec_interleave_low_n_lemma_uint32_8_4 v2'' v6'';
  let r4'': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v4.(2) v5.(2) v6.(2) v7.(2) in
  assert (vec_v v4''' == r4'');

  let v5''' = vec_interleave_high_n 4 v2'' v6'' in
  vec_interleave_high_n_lemma_uint32_8_4 v2'' v6'';
  let r5'': lseq uint32 8 = create8 v0.(6) v1.(6) v2.(6) v3.(6) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v5''' == r5'');

  let v6''' = vec_interleave_low_n 4 v3'' v7'' in
  vec_interleave_low_n_lemma_uint32_8_4 v3'' v7'';
  let r6'': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v4.(3) v5.(3) v6.(3) v7.(3) in
  assert (vec_v v6''' == r6'');

  let v7''' = vec_interleave_high_n 4 v3'' v7'' in
  vec_interleave_high_n_lemma_uint32_8_4 v3'' v7'';
  let r7'': lseq uint32 8 = create8 v0.(7) v1.(7) v2.(7) v3.(7) v4.(7) v5.(7) v6.(7) v7.(7) in
  assert (vec_v v7''' == r7'');
  let res = create8 v0''' v2''' v4''' v6''' v1''' v3''' v5''' v7''' in
  ()


let transpose8x8_lemma #t vs =
  match t with
  | U32 -> Classical.forall_intro_2 (transpose8x8_uint32_lemma_ij vs)
  | _ -> admit()

let transpose16x16_lemma #t vs = admit()
