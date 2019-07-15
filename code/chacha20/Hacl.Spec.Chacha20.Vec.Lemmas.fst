module Hacl.Spec.Chacha20.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Scalar = Spec.Chacha20
open Hacl.Spec.Chacha20.Vec

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val line_lemma_i:
    #w:lanes
  -> a:idx -> b:idx -> d:idx
  -> s:rotval U32 -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (line #w a b d s m)).[i] == Scalar.line a b d s (transpose_state #w m).[i])
let line_lemma_i #w a b d s m i =
  eq_intro (transpose_state (line #w a b d s m)).[i] (Scalar.line a b d s (transpose_state #w m).[i])

#set-options "--z3rlimit 50"

val quarter_round_lemma_i:
    #w:lanes
  -> a:idx -> b:idx -> c:idx -> d:idx
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (quarter_round #w a b c d m)).[i] == Scalar.quarter_round a b c d (transpose_state m).[i])
let quarter_round_lemma_i #w a b c d m i =
  let lp0 = line a b d (size 16) m in
  let lp1 = line c d b (size 12) lp0 in
  let lp2 = line a b d (size 8) lp1 in
  let lp3 = line c d b (size 7) lp2 in
  assert (quarter_round #w a b c d m == lp3);
  line_lemma_i a b d (size 16) m i;
  line_lemma_i c d b (size 12) lp0 i;
  line_lemma_i a b d (size 8) lp1 i;
  line_lemma_i c d b (size 7) lp2 i;
  eq_intro (transpose_state (quarter_round #w a b c d m)).[i] (Scalar.quarter_round a b c d (transpose_state m).[i])

val column_round_lemma_i:
    #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (column_round #w m)).[i] == Scalar.column_round (transpose_state m).[i])
let column_round_lemma_i #w m i =
  let lp0 = quarter_round 0 4 8  12 m in
  let lp1 = quarter_round 1 5 9  13 lp0 in
  let lp2 = quarter_round 2 6 10 14 lp1 in
  let lp3 = quarter_round 3 7 11 15 lp2 in
  assert (column_round #w m == lp3);
  quarter_round_lemma_i 0 4 8  12 m i;
  quarter_round_lemma_i 1 5 9  13 lp0 i;
  quarter_round_lemma_i 2 6 10 14 lp1 i;
  quarter_round_lemma_i 3 7 11 15 lp2 i;
  eq_intro (transpose_state (column_round #w m)).[i] (Scalar.column_round (transpose_state m).[i])

val diagonal_round_lemma_i:
    #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (diagonal_round #w m)).[i] == Scalar.diagonal_round (transpose_state m).[i])
let diagonal_round_lemma_i #w m i =
  let lp0 = quarter_round 0 5 10 15 m in
  let lp1 = quarter_round 1 6 11 12 lp0 in
  let lp2 = quarter_round 2 7 8  13 lp1 in
  let lp3 = quarter_round 3 4 9  14 lp2 in
  assert (diagonal_round #w m == lp3);
  quarter_round_lemma_i 0 5 10 15 m i;
  quarter_round_lemma_i 1 6 11 12 lp0 i;
  quarter_round_lemma_i 2 7 8  13 lp1 i;
  quarter_round_lemma_i 3 4 9  14 lp2 i;
  eq_intro (transpose_state (diagonal_round #w m)).[i] (Scalar.diagonal_round (transpose_state m).[i])

val double_round_map_lemma_i:
    #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (double_round #w m)).[i] == Scalar.double_round (transpose_state m).[i])
let double_round_map_lemma_i #w m i =
  let m1 = column_round m in
  let m2 = diagonal_round m1 in
  column_round_lemma_i m i;
  diagonal_round_lemma_i m1 i

let scalar_rounds (m:Scalar.state) : Scalar.state =
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round m)))))))))

val scalar_rounds_unroll_lemma: m:Scalar.state ->
  Lemma (scalar_rounds m == Scalar.rounds m)
let scalar_rounds_unroll_lemma m =
  let open Lib.LoopCombinators in
  eq_repeat0 Scalar.double_round m;
  unfold_repeat 10 Scalar.double_round m 0;
  unfold_repeat 10 Scalar.double_round m 1;
  unfold_repeat 10 Scalar.double_round m 2;
  unfold_repeat 10 Scalar.double_round m 3;
  unfold_repeat 10 Scalar.double_round m 4;
  unfold_repeat 10 Scalar.double_round m 5;
  unfold_repeat 10 Scalar.double_round m 6;
  unfold_repeat 10 Scalar.double_round m 7;
  unfold_repeat 10 Scalar.double_round m 8;
  unfold_repeat 10 Scalar.double_round m 9

val rounds_lemma_i:
    #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (rounds #w m)).[i] == Scalar.rounds (transpose_state m).[i])
let rounds_lemma_i #w m i =
  let ms = (transpose_state m).[i] in
  let m1 = double_round m in
  let m2 = double_round m1 in
  let m3 = double_round m2 in
  let m4 = double_round m3 in
  let m5 = double_round m4 in
  let m6 = double_round m5 in
  let m7 = double_round m6 in
  let m8 = double_round m7 in
  let m9 = double_round m8 in
  let m10 = double_round m9 in
  assert (rounds m == m10);
  double_round_map_lemma_i #w m i;
  double_round_map_lemma_i #w m1 i;
  double_round_map_lemma_i #w m2 i;
  double_round_map_lemma_i #w m3 i;
  double_round_map_lemma_i #w m4 i;
  double_round_map_lemma_i #w m5 i;
  double_round_map_lemma_i #w m6 i;
  double_round_map_lemma_i #w m7 i;
  double_round_map_lemma_i #w m8 i;
  double_round_map_lemma_i #w m9 i;
  assert ((transpose_state m10).[i] == scalar_rounds ms);
  scalar_rounds_unroll_lemma ms

val sum_state_lemma_i:
    #w:lanes
  -> st1:state w
  -> st2:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (sum_state st1 st2)).[i] ==
	 Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])
let sum_state_lemma_i #w st1 st2 i =
  eq_intro (transpose_state (sum_state st1 st2)).[i]
	   (Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])

val add_counter_lemma_i:
    #w:lanes
  -> st:state w
  -> ctr:counter{w * ctr <= max_size_t}
  -> i:nat{i < w} ->
  Lemma ((transpose_state (add_counter #w ctr st)).[i] ==
	 Scalar.chacha20_add_counter (transpose_state st).[i] (w * ctr))
let add_counter_lemma_i #w st ctr i =
  FStar.Math.Lemmas.modulo_lemma (w * ctr) (pow2 32);
  assert (v (u32 w *! u32 ctr) == v (u32 (w * ctr)));
  eq_intro (transpose_state (add_counter #w ctr st)).[i]
	   (Scalar.chacha20_add_counter (transpose_state st).[i] (w * ctr))

val chacha20_core_lemma_i:
    #w:lanes
  -> ctr:counter{w * ctr <= max_size_t}
  -> s0:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (chacha20_core ctr s0)).[i] ==
	 Scalar.chacha20_core (w * ctr) (transpose_state s0).[i])
let chacha20_core_lemma_i #w ctr s0 i =
  let k0 = add_counter ctr s0 in
  add_counter_lemma_i s0 ctr i;
  let k1 = rounds k0 in
  rounds_lemma_i k0 i;
  let k2 = sum_state k1 s0 in
  sum_state_lemma_i k1 s0 i;
  let k3 = add_counter ctr k2 in
  add_counter_lemma_i k2 ctr i

val chacha20_init_equiv_lemma:
    k:key
  -> n:nonce
  -> ctr0:counter ->
  Lemma (
    let uc = map secret chacha20_constants in
    let uk = uints_from_bytes_le #U32 #SEC #8 k in
    let uctr = create 1 (u32 ctr0) in
    let un = uints_from_bytes_le #U32 #SEC #3 n in
    Scalar.chacha20_init k n ctr0 == uc @| uk @| uctr @| un)
let chacha20_init_equiv_lemma k n ctr0 =
  let uc = map secret chacha20_constants in
  let uk = uints_from_bytes_le #U32 #SEC #8 k in
  let uctr = create 1 (u32 ctr0) in
  let un = uints_from_bytes_le #U32 #SEC #3 n in
  let res = uc @| uk @| uctr @| un in
  assert (res == concat uc (concat uk (concat uctr un)));
  eq_intro res (concat (concat (concat uc uk) uctr) un);
  let len0 = 4 in
  let len1 = 8 in
  let len2 = 1 in
  let len3 = 3 in

  let res = concat (concat (concat uc uk) uctr) un in
  let st = create 16 (u32 0) in
  let st = update_sub st 0 4 (map secret chacha20_constants) in
  let st = update_sub st 4 8 (uints_from_bytes_le #U32 #SEC #8 k) in
  eq_intro (sub st 0 4) uc;
  let st = st.[12] <- u32 ctr0 in
  eq_intro (sub st 0 4) uc;
  eq_intro (sub st 4 8) uk;
  let res1 = update_sub st 13 3 (uints_from_bytes_le #U32 #SEC #3 n) in
  eq_intro (sub res1 0 4) uc;
  eq_intro (sub res1 4 8) uk;
  eq_intro (sub res1 12 1) uctr;
  eq_intro (sub res1 13 3) un;

  FStar.Seq.Properties.lemma_split (sub res 0 (len0 + len1)) len0;
  FStar.Seq.Properties.lemma_split (sub res1 0 (len0 + len1)) len0;

  FStar.Seq.Properties.lemma_split (sub res 0 (len0 + len1 + len2)) (len0 + len1);
  FStar.Seq.Properties.lemma_split (sub res1 0 (len0 + len1 + len2)) (len0 + len1);

  FStar.Seq.Properties.lemma_split res (len0 + len1 + len2);
  FStar.Seq.Properties.lemma_split res1 (len0 + len1 + len2)

val chacha20_init_lemma_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> i:nat{i < w} ->
  Lemma (
    (transpose_state (chacha20_init #w k n ctr0)).[i] ==
      Scalar.chacha20_init k n (ctr0 + i))
let chacha20_init_lemma_i #w k n ctr0 i =
  let st1 = setup1 k n ctr0 in
  assert (st1 == Scalar.chacha20_init k n ctr0);
  assert (st1.[12] == u32 ctr0);

  let st = map (vec_load_i w) st1 in
  eq_intro (transpose_state st).[i] st1;
  assert ((transpose_state st).[i] == st1);

  let c = vec_counter U32 w in
  assert ((vec_v c).[i] == u32 i);

  let res = st.[12] <- st.[12] +| c in
  let res1 = st1.[12] <- st1.[12] +. u32 i in
  eq_intro (transpose_state res).[i] res1;
  assert ((transpose_state res).[i] == res1);
  assert (res1.[12] == u32 ctr0 +. u32 i);
  assert (v (u32 ctr0 +. u32 i) == v (u32 (ctr0 + i)));
  assert (res1.[12] == u32 (ctr0 + i));

  let res2 = Scalar.chacha20_init k n (ctr0 + i) in
  chacha20_init_equiv_lemma k n ctr0;
  chacha20_init_equiv_lemma k n (ctr0 + i);
  eq_intro res1 res2

val load_blocks_lemma_index:
    #w:lanes
  -> b:blocks w
  -> i:nat{i < w * 16} ->
  Lemma ((vec_v (load_blocks #w b).[i / w]).[i % w] == uint_from_bytes_le (sub b (4 * i) 4))
let load_blocks_lemma_index #w b i =
  let j = i / w in
  let res = load_blocks #w b in
  assert (res.[j] == load_blocks_inner #w b j);
  assert (res.[j] == vec_from_bytes_le U32 w (sub b (j * w * 4) (w * 4)));
  assert (vec_v res.[j] == uints_from_bytes_le (sub b (j * w * 4) (w * 4)));
  let j1 = i % w in
  let b_j = sub b (j * w * 4) (w * 4) in
  index_uints_from_bytes_le #U32 b_j j1;
  assert ((vec_v res.[j]).[j1] == uint_from_bytes_le (sub b_j (j1 * 4) 4));
  FStar.Seq.slice_slice b (j * w * 4) (j * w * 4 + w * 4) (j1 * 4) (j1 * 4 + 4);
  assert (j * w * 4 + j1 * 4 == 4 * i);
  assert (j * w * 4 + j1 * 4 + 4 == 4 * (i + 1));
  assert ((vec_v res.[j]).[j1] == uint_from_bytes_le (slice b (4 * i) (4 * (i + 1))))

val store_blocks_lemma_aux:
  #w:lanes -> i:nat ->
  Lemma ((i % (w * 4)) / 4 == (i / 4) % w)
let store_blocks_lemma_aux #w i = ()

val store_blocks_lemma_index:
    #w:lanes
  -> st:state w
  -> i:nat{i < w * size_block} ->
  Lemma (
    let j = i / 4 in
    (store_blocks #w st).[i] == (uint_to_bytes_le (vec_v st.[j / w ]).[j % w]).[i % 4])
let store_blocks_lemma_index #w st i =
  let res = store_blocks #w st in
  index_generate_blocks (w * 4) 16 16 (store_blocks_inner #w st) i;
  let j = i / (w * 4) in
  let _, s2 = store_blocks_inner #w st j () in
  assert (Seq.index res i == Seq.index s2 (i % (w * 4)));
  assert (s2 == vec_to_bytes_le st.[j]);
  assert (s2 == uints_to_bytes_le (vec_v st.[j]));
  index_uints_to_bytes_le (vec_v st.[j]) (i % (w * 4));

  assert (Seq.index s2 (i % (w * 4)) == (uint_to_bytes_le (vec_v st.[j]).[(i % (w * 4)) / 4]).[(i % (w * 4)) % 4]);
  assert ((i % (w * 4)) % 4 == i % 4);
  assert (Seq.index res i == (uint_to_bytes_le (vec_v st.[j]).[(i % (w * 4)) / 4]).[i % 4]);
  FStar.Math.Lemmas.division_multiplication_lemma i 4 w;
  store_blocks_lemma_aux #w i

val xor_block_scalar_lemma_index:
    k:Scalar.state
  -> b:Scalar.block
  -> i:nat{i < size_block} ->
  Lemma (
    let j = i / 4 in
    (Scalar.xor_block k b).[i] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. k.[j])).[i % 4])
let xor_block_scalar_lemma_index k b i =
  let ib = uints_from_bytes_le b in
  let ob = map2 (^.) ib k in
  let res = uints_to_bytes_le ob in
  index_uints_to_bytes_le ob i;
  assert (res.[i] == (uint_to_bytes_le ob.[i / 4]).[i % 4]);
  assert (ob.[i / 4] == ib.[i / 4] ^. k.[i / 4]);
  index_uints_from_bytes_le #U32 #SEC #16 b (i / 4);
  assert (ib.[i / 4] == uint_from_bytes_le (sub b (i / 4 * 4) 4));
  assert (res.[i] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (i / 4 * 4) 4)) ^. k.[i / 4])).[i % 4])

inline_for_extraction
let transpose4x4 (vs:lseq (uint32xN 4) 4) : lseq (uint32xN 4) 4 =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let (v0'',v1'',v2'',v3'') = transpose4x4 (v0,v1,v2,v3) in
  create4 v0'' v1'' v2'' v3''

val transpose4x4_lemma_ij: vs:lseq (uint32xN 4) 4 -> i:nat{i < 4} -> j:nat{j < 4} ->
  Lemma (
    let res = transpose4x4 vs in
    (vec_v res.[i]).[j] == (vec_v vs.[j]).[i])
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
  Lemma (
    let res = transpose4x4 vs in
    (forall (i:nat{i < 4}) (j:nat{j < 4}). (vec_v res.[i]).[j] == (vec_v vs.[j]).[i]))
let transpose4x4_lemma vs =
  Classical.forall_intro_2 (transpose4x4_lemma_ij vs)

val transpose4_lemma:
    k:state 4
  -> i:nat{i < 16 * 4} ->
  Lemma (
    (vec_v (transpose4 k).[i / 4]).[i % 4] == ((transpose_state k).[i / 16]).[i % 16])
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

inline_for_extraction
let transpose8x8 (vs:lseq (uint32xN 8) 8) : lseq (uint32xN 8) 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (vs.[0],vs.[1],vs.[2],vs.[3],vs.[4],vs.[5],vs.[6],vs.[7]) in
  let (v0''', v2''', v4''', v6''', v1''', v3''', v5''', v7''') = transpose8x8 (v0,v1,v2,v3,v4,v5,v6,v7) in
  create8 v0''' v2''' v4''' v6''' v1''' v3''' v5''' v7'''

unfold
let op_Array_Access (#w:lanes) (a:uint32xN w) i = (vec_v a).[i]

val transpose8x8_lemma_ij: vs:lseq (uint32xN 8) 8 -> i:nat{i < 8} -> j:nat{j < 8} ->
  Lemma (
    let res = transpose8x8 vs in
    (vec_v res.[i]).[j] == (vec_v vs.[j]).[i])
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
  Lemma (
    let res = transpose8x8 vs in
    (forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v res.[i]).[j] == (vec_v vs.[j]).[i]))
let transpose8x8_lemma vs =
  Classical.forall_intro_2 (transpose8x8_lemma_ij vs)

val transpose8_lemma:
    k:state 8
  -> i:nat{i < 16 * 8} ->
  Lemma (
    (vec_v (transpose8 k).[i / 8]).[i % 8] == ((transpose_state k).[i / 16]).[i % 16])
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
  Lemma (
    (vec_v (transpose #w k).[i / w]).[i % w] == ((transpose_state k).[i / 16]).[i % 16])
let transpose_lemma_index #w k i =
  match w with
  | 1 -> ()
  | 4 -> transpose4_lemma k i
  | 8 -> transpose8_lemma k i

val xor_block_lemma_aux1: i:nat ->
  Lemma (i / 4 % 16 == (i % size_block) / 4)
let xor_block_lemma_aux1 i = ()

val xor_block_lemma_aux2: i:nat ->
  Lemma (i / size_block * size_block + 4 * ((i % size_block) / 4) == 4 * (i / 4))
let xor_block_lemma_aux2 i = ()

val xor_block_lemma_aux3: i:nat ->
  Lemma (i / size_block * size_block + 4 * ((i % size_block) / 4 + 1) == 4 * (i / 4 + 1))
let xor_block_lemma_aux3 i = ()

val xor_block_scalar_lemma_index_aux:
    #w:lanes
  -> k:state w
  -> b:blocks w
  -> i:nat{i < w * size_block} ->
  Lemma (
    let j = i / 4 in
    (Scalar.xor_block (transpose_state k).[i / size_block] (sub b (i / size_block * size_block) size_block)).[i % size_block] ==
    (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. ((transpose_state k).[i / size_block]).[j % 16])).[i % 4])
let xor_block_scalar_lemma_index_aux #w k b i =
  let j = i / size_block in
  let b_j = sub b (j * size_block) size_block in
  let res = Scalar.xor_block (transpose_state k).[j] b_j in
  let j1 = i % size_block in
  xor_block_scalar_lemma_index (transpose_state k).[j] b_j j1;
  let j2 = j1 / 4 in
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b_j (4 * j2) 4)) ^. ((transpose_state k).[j]).[j2])).[j1 % 4]);
  xor_block_lemma_aux2 i;
  xor_block_lemma_aux3 i;
  FStar.Seq.Properties.slice_slice b (j * size_block) ((j + 1) * size_block) (4 * j2) (4 * (j2 + 1));
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * (i / 4)) 4)) ^. ((transpose_state k).[j]).[j2])).[j1 % 4]);
  xor_block_lemma_aux1 i;
  assert (j2 == i / 4 % 16);
  assert (j1 % 4 == i % 4);
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * (i / 4)) 4)) ^. ((transpose_state k).[j]).[i / 4 % 16])).[i % 4])

val xor_block_lemma_index:
    #w:lanes
  -> k:state w
  -> b:blocks w
  -> i:nat{i < w * size_block} ->
  Lemma (
    (xor_block k b).[i] ==
    index (Scalar.xor_block (transpose_state k).[i / size_block]
      (sub b (i / size_block * size_block) size_block)) (i % size_block))
let xor_block_lemma_index #w k b i =
  let ib = load_blocks b in
  let kb = transpose k in
  let ob = map2 (^|) ib kb in
  let res = store_blocks ob in
  store_blocks_lemma_index #w ob i;
  let j = i / 4 in
  assert (index res i == (uint_to_bytes_le (vec_v ob.[j / w]).[j % w]).[i % 4]);
  assert (vec_v ob.[j / w] == vec_v (ib.[j / w] ^| kb.[j / w]));
  assert ((vec_v ob.[j / w]).[j % w] == (vec_v ib.[j / w]).[j % w] ^. (vec_v kb.[j / w]).[j % w]);
  load_blocks_lemma_index #w b j;
  assert ((vec_v ib.[j / w]).[j % w] == uint_from_bytes_le (sub b (4 * j) 4));
  assert ((vec_v ob.[j / w]).[j % w] == uint_from_bytes_le (sub b (4 * j) 4) ^. (vec_v kb.[j / w]).[j % w]);
  assert (res.[i] == (uint_to_bytes_le (uint_from_bytes_le (sub b (4 * j) 4) ^. (vec_v kb.[j / w]).[j % w])).[i % 4]);
  transpose_lemma_index #w k j;
  FStar.Math.Lemmas.division_multiplication_lemma i 4 16;
  assert (j / 16 == i / 64);
  assert (res.[i] == (uint_to_bytes_le (uint_from_bytes_le (sub b (4 * j) 4) ^. ((transpose_state k).[i / 64]).[j % 16])).[i % 4]);
  let res1 = Scalar.xor_block (transpose_state k).[i / size_block] (sub b (i / size_block * size_block) size_block) in
  xor_block_scalar_lemma_index_aux #w k b i;
  assert (res1.[i % size_block] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. ((transpose_state k).[i / size_block]).[j % 16])).[i % 4]);
  assert (res.[i] == res1.[i % size_block])

val chacha20_encrypt_block_lemma_index:
    #w:lanes
  -> st0:state w
  -> incr:counter{w * incr <= max_size_t}
  -> b:blocks w
  -> j:nat{j < w * size_block} ->
  Lemma (
    let j1 = j / size_block in
    FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
    let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
    Seq.index (chacha20_encrypt_block st0 incr b) j ==
    Seq.index (Scalar.chacha20_encrypt_block (transpose_state st0).[j1] (w * incr) b_j1) (j % size_block))
let chacha20_encrypt_block_lemma_index #w st0 incr b j =
  let k = chacha20_core incr st0 in
  chacha20_core_lemma_i #w incr st0 (j / size_block);
  let res = xor_block k b in
  xor_block_lemma_index #w k b j

val chacha20_encrypt_last_lemma_index_aux:
    #w:lanes
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len ->
  Lemma (
    let nb = len / size_block in
    let rem = len % size_block in
    let last = Seq.slice b (nb * size_block) len in
    let plain1 = create size_block (u8 0) in
    let plain1 = update_sub plain1 0 rem last in
    let plain = create (w*size_block) (u8 0) in
    let plain = update_sub plain 0 len b in
    let last_plain = Seq.slice plain (nb*size_block) ((nb+1)*size_block) in
    plain1 == last_plain)
let chacha20_encrypt_last_lemma_index_aux #w len b =
  let nb = len / size_block in
  let rem = len % size_block in
  let last = Seq.slice b (nb * size_block) len in

  let plain1 = create size_block (u8 0) in
  let plain1 = update_sub plain1 0 rem last in
  let zeroes1 = create (size_block - rem) (u8 0) in
  FStar.Seq.Properties.lemma_split plain1 rem;
  FStar.Seq.Properties.lemma_split (Seq.append last zeroes1) rem;
  eq_intro plain1 (Seq.append last zeroes1);
  assert (plain1 == Seq.append last zeroes1);

  let plain = create (w*size_block) (u8 0) in
  let plain = update_sub plain 0 len b in
  let zeroes2 = create (w*size_block - len) (u8 0) in
  FStar.Seq.Properties.lemma_split plain len;
  FStar.Seq.Properties.lemma_split (Seq.append b zeroes2) len;
  eq_intro plain (Seq.append b zeroes2);
  assert (plain == Seq.append b zeroes2);

  let last_plain = Seq.slice plain (nb*size_block) ((nb+1)*size_block) in
  FStar.Seq.Properties.lemma_split last_plain rem;
  eq_intro plain1 last_plain;
  assert (plain1 == last_plain)

#set-options "--z3rlimit 150"

val chacha20_encrypt_last_lemma_index:
    #w:lanes
  -> st0:state w
  -> incr:counter{w * incr <= max_size_t}
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len
  -> j:nat{j < len} ->
  Lemma (
    let nb = len / size_block in
    let rem = len % size_block in
    FStar.Seq.lemma_len_slice b (nb * size_block) len;
    let last = Seq.slice b (nb * size_block) len in

    if j < nb * size_block then begin
      let j1 = j / size_block in
      FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
      let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_block (transpose_state st0).[j1] (w * incr) b_j1) (j % size_block) end
   else
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_last (transpose_state st0).[nb] (w * incr) rem last) (j % size_block))
let chacha20_encrypt_last_lemma_index #w st0 incr len b j =
  let plain = create (w*size_block) (u8 0) in
  let plain = update_sub plain 0 len b in
  let res = chacha20_encrypt_last st0 incr len b in
  assert (res == Seq.slice (chacha20_encrypt_block st0 incr plain) 0 len);

  let j1 = j / size_block in
  FStar.Seq.lemma_len_slice plain (j1*size_block) ((j1+1)*size_block);
  let b_j1 = Seq.slice plain (j1*size_block) ((j1+1)*size_block) in
  let res1 = chacha20_encrypt_block st0 incr plain in
  chacha20_encrypt_block_lemma_index #w st0 incr plain j;

  assert (
    Seq.index (chacha20_encrypt_block st0 incr plain) j ==
    Seq.index (Scalar.chacha20_encrypt_block (transpose_state st0).[j1] (w * incr) b_j1) (j % size_block));

  let nb = len / size_block in

  if j < nb * size_block then begin
    FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
    let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
    assert (
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_block (transpose_state st0).[j1] (w * incr) b_j1) (j % size_block)) end
   else begin
     let rem = len % size_block in
     let last_plain = Seq.slice plain (nb*size_block) ((nb+1)*size_block) in
     let last = Seq.slice b (nb * size_block) len in
     let plain1 = create size_block (u8 0) in
     let plain1 = update_sub plain1 0 rem last in
     chacha20_encrypt_last_lemma_index_aux #w len b;
     assert (plain1 == last_plain);

     assert (
       Scalar.chacha20_encrypt_last (transpose_state st0).[nb] (w * incr) rem last ==
       Seq.slice (Scalar.chacha20_encrypt_block (transpose_state st0).[nb] (w * incr) plain1) 0 rem);

     assert (
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_last (transpose_state st0).[nb] (w * incr) rem last) (j % size_block)) end

val add_counter_lemma_aux:
    ctr0:counter
  -> w:lanes
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> i:nat{i < w}
  -> b:uint32 ->
  Lemma (b +. u32 ctr0 +. u32 (w * incr + i) == b +. u32 (ctr0 + i) +. u32 (w * incr))
let add_counter_lemma_aux ctr0 w incr i b =
  let lp = b +. u32 ctr0 +. u32 (w * incr + i) in
  let rp = b +. u32 (ctr0 + i) +. u32 (w * incr) in
  assert (v lp == ((v b + ctr0) % modulus U32 + (w * incr + i)) % modulus U32);
  assert (v rp == ((v b + ctr0 + i) % modulus U32 + (w * incr)) % modulus U32);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v b + ctr0) (w * incr + i) (modulus U32);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v b + ctr0 + i) (w * incr) (modulus U32)

val chacha20_core_equiv_lemma:
    ctr0:counter
  -> st1:Scalar.state
  -> st2:Scalar.state
  -> w:lanes
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> i:nat{i < w} ->
  Lemma
    (requires (
      forall (j:nat). j < 16 /\ j <> 12 ==> st1.[j] == st2.[j] /\
      st1.[12] == u32 ctr0 /\ st2.[12] == u32 (ctr0 + i)))
    (ensures
      Scalar.chacha20_core (w * incr + i) st1 ==
      Scalar.chacha20_core (w * incr) st2)
let chacha20_core_equiv_lemma ctr0 st1 st2 w incr i =
  let k1 = Scalar.chacha20_add_counter st1 (w * incr + i) in
  assert (k1.[12] == u32 ctr0 +. u32 (w * incr + i));
  let k2 = Scalar.chacha20_add_counter st2 (w * incr) in
  assert (k2.[12] == u32 (ctr0 + i) +. u32 (w * incr));
  assert (v k1.[12] == v k2.[12]);
  eq_intro k1 k2;
  let k = Scalar.rounds k1 in
  let k1 = Scalar.sum_state k st1 in
  assert (k1.[12] == k.[12] +. u32 ctr0);
  let k2 = Scalar.sum_state k st2 in
  assert (k2.[12] == k.[12] +. u32 (ctr0 + i));
  assert (forall (j:nat). j < 16 /\ j <> 12 ==> k1.[j] == k2.[j]);
  let k1 = Scalar.chacha20_add_counter k1 (w * incr + i) in
  assert (k1.[12] == k.[12] +. u32 ctr0 +. u32 (w * incr + i));
  let k2 = Scalar.chacha20_add_counter k2 (w * incr) in
  assert (k2.[12] == k.[12] +. u32 (ctr0 + i) +. u32 (w * incr));
  add_counter_lemma_aux ctr0 w incr i k.[12];
  eq_intro k1 k2

val chacha20_encrypt_block_equiv_lemma_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> st0:state w{st0 == chacha20_init #w k n ctr0}
  -> ctx:Scalar.state{ctx == Scalar.chacha20_init k n ctr0}
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> b_i:Scalar.block
  -> i:nat{i < w} ->
  Lemma (
    Scalar.chacha20_encrypt_block ctx (w * incr + i) b_i ==
      Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr) b_i)
let chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 st0 ctx incr b i =
  assert (ctx == Scalar.chacha20_init k n ctr0);
  assert (st0 == chacha20_init #w k n ctr0);
  chacha20_init_lemma_i #w k n ctr0 i;
  assert ((transpose_state st0).[i] == Scalar.chacha20_init k n (ctr0 + i));
  chacha20_init_equiv_lemma k n ctr0;
  chacha20_init_equiv_lemma k n (ctr0 + i);
  let st_s = (transpose_state st0).[i] in
  assert (st_s.[12] == u32 (ctr0 + i));
  assert (ctx.[12] == u32 ctr0);
  assert (forall (j:nat). j < 16 /\ j <> 12 ==> ctx.[j] == st_s.[j]);
  chacha20_core_equiv_lemma ctr0 ctx st_s w incr i

val chacha20_encrypt_block_equiv_lemma_index:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> b:blocks w
  -> j:nat{j < w * size_block} ->
  Lemma (
    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    FStar.Math.Lemmas.cancel_mul_div w size_block;
    let j1 = j / size_block in
    FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
    let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in

    Seq.index (chacha20_encrypt_block st0 incr b) j ==
      Seq.index (Scalar.chacha20_encrypt_block ctx (w * incr + j1) b_j1) (j % size_block))
let chacha20_encrypt_block_equiv_lemma_index #w k n ctr0 incr b j =
  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  chacha20_encrypt_block_lemma_index #w st0 incr b j;
  let j1 = j / size_block in
  FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
  let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
  chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 st0 ctx incr b_j1 j1

val chacha20_encrypt_last_equiv_lemma_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> st0:state w{st0 == chacha20_init #w k n ctr0}
  -> ctx:Scalar.state{ctx == Scalar.chacha20_init k n ctr0}
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> len:size_nat{len < size_block}
  -> b_i:lbytes len
  -> i:nat{i < w} ->
  Lemma (
    Scalar.chacha20_encrypt_last ctx (w * incr + i) len b_i ==
      Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr) len b_i)
let chacha20_encrypt_last_equiv_lemma_i #w k n ctr0 st0 ctx incr len b i =
  let plain = create size_block (u8 0) in
  let plain = update_sub plain 0 len b in
  chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 st0 ctx incr plain i

val chacha20_encrypt_last_equiv_lemma_index:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len
  -> j:nat{j < len} ->
  Lemma (
    let st0 = chacha20_init #w k n ctr0 in
    let ctx = Scalar.chacha20_init k n ctr0 in
    let nb = len / size_block in
    let rem = len % size_block in
    FStar.Seq.lemma_len_slice b (nb * size_block) len;
    let last = Seq.slice b (nb * size_block) len in

    if j < nb * size_block then begin
      let j1 = j / size_block in
      FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
      let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_block ctx (w * incr + j1) b_j1) (j % size_block) end
   else
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_last ctx (w * incr + nb) rem last) (j % size_block))
let chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 incr len b j =
  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  chacha20_encrypt_last_lemma_index #w st0 incr len b j;

  let nb = len / size_block in
  let rem = len % size_block in
  FStar.Seq.lemma_len_slice b (nb * size_block) len;
  let last = Seq.slice b (nb * size_block) len in
  FStar.Math.Lemmas.cancel_mul_div nb size_block;
  if j < nb * size_block then begin
    let j1 = j / size_block in
    FStar.Seq.lemma_len_slice b (j1*size_block) ((j1+1)*size_block);
    let b_j1 = Seq.slice b (j1*size_block) ((j1+1)*size_block) in
    assert (
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_block (transpose_state st0).[j1] (w * incr) b_j1) (j % size_block));
      chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 st0 ctx incr b_j1 j1 end
   else begin
     assert (
      Seq.index (chacha20_encrypt_last st0 incr len b) j ==
      Seq.index (Scalar.chacha20_encrypt_last (transpose_state st0).[nb] (w * incr) rem last) (j % size_block));
     chacha20_encrypt_last_equiv_lemma_i #w k n ctr0 st0 ctx incr rem last nb end
