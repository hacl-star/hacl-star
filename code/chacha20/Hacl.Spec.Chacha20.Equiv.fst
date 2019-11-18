module Hacl.Spec.Chacha20.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas
open Lib.ByteSequence
open Lib.IntVector

module Scalar = Spec.Chacha20
module Lemmas = Hacl.Spec.Chacha20.Lemmas
open Hacl.Spec.Chacha20.Vec


#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val line_lemma_i:
    #w:lanes
  -> a:idx -> b:idx -> d:idx
  -> s:rotval U32 -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (line #w a b d s m)).[i] `Seq.equal` Scalar.line a b d s (transpose_state #w m).[i])
let line_lemma_i #w a b d s m i =
  eq_intro (transpose_state (line #w a b d s m)).[i] (Scalar.line a b d s (transpose_state #w m).[i])


#set-options "--z3rlimit 50"

val quarter_round_lemma_i:
    #w:lanes
  -> a:idx -> b:idx -> c:idx -> d:idx
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (quarter_round #w a b c d m)).[i] `Seq.equal` Scalar.quarter_round a b c d (transpose_state m).[i])
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
  Lemma ((transpose_state (column_round #w m)).[i] `Seq.equal` Scalar.column_round (transpose_state m).[i])
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
  Lemma ((transpose_state (diagonal_round #w m)).[i] `Seq.equal` Scalar.diagonal_round (transpose_state m).[i])
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
  Lemma ((transpose_state (double_round #w m)).[i] `Seq.equal` Scalar.double_round (transpose_state m).[i])
let double_round_map_lemma_i #w m i =
  let m1 = column_round m in
  let m2 = diagonal_round m1 in
  column_round_lemma_i m i;
  diagonal_round_lemma_i m1 i


noextract
let scalar_rounds (m:Scalar.state) : Scalar.state =
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round m)))))))))


val scalar_rounds_unroll_lemma: m:Scalar.state ->
  Lemma (scalar_rounds m `Seq.equal` Scalar.rounds m)
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
  Lemma ((transpose_state (rounds #w m)).[i] `Seq.equal` Scalar.rounds (transpose_state m).[i])
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
  Lemma ((transpose_state (sum_state st1 st2)).[i] `Seq.equal` Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])
let sum_state_lemma_i #w st1 st2 i =
  eq_intro (transpose_state (sum_state st1 st2)).[i] (Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])


val add_counter_lemma_i:
    #w:lanes
  -> st:state w
  -> ctr:counter{w * ctr <= max_size_t}
  -> i:nat{i < w} ->
  Lemma ((transpose_state (add_counter #w ctr st)).[i] `Seq.equal` Scalar.chacha20_add_counter (transpose_state st).[i] (w * ctr))
let add_counter_lemma_i #w st ctr i =
  FStar.Math.Lemmas.modulo_lemma (w * ctr) (pow2 32);
  assert (v (u32 w *! u32 ctr) == v (u32 (w * ctr)));
  eq_intro (transpose_state (add_counter #w ctr st)).[i] (Scalar.chacha20_add_counter (transpose_state st).[i] (w * ctr))


val chacha20_core_lemma_i:
    #w:lanes
  -> ctr:counter{w * ctr <= max_size_t}
  -> s0:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (chacha20_core ctr s0)).[i] `Seq.equal` Scalar.chacha20_core (w * ctr) (transpose_state s0).[i])
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
  Lemma
  (let uc = map secret chacha20_constants in
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
  Lemma ((transpose_state (chacha20_init #w k n ctr0)).[i] `Seq.equal` Scalar.chacha20_init k n (ctr0 + i))
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
  let j1 = i % w in
  let b_j = sub b (j * w * 4) (w * 4) in

  let res = load_blocks #w b in
  assert (vec_v res.[j] == uints_from_bytes_le b_j);

  index_uints_from_bytes_le #U32 b_j j1;
  assert ((vec_v res.[j]).[j1] == uint_from_bytes_le (sub b_j (j1 * 4) 4));
  FStar.Seq.slice_slice b (j * w * 4) (j * w * 4 + w * 4) (j1 * 4) (j1 * 4 + 4);
  assert (j * w * 4 + j1 * 4 == 4 * i);
  assert (j * w * 4 + j1 * 4 + 4 == 4 * (i + 1));
  assert ((vec_v res.[j]).[j1] == uint_from_bytes_le (slice b (4 * i) (4 * (i + 1))))


val store_blocks_lemma_index:
    #w:lanes
  -> st:state w
  -> i:nat{i < w * size_block} ->
  Lemma
  (let j = i / 4 in
  (store_blocks #w st).[i] == (uint_to_bytes_le (vec_v st.[j / w ]).[j % w]).[i % 4])
let store_blocks_lemma_index #w st i =
  let res = store_blocks #w st in
  index_generate_blocks (w * 4) 16 16 (store_blocks_inner #w st) i;
  let j = i / (w * 4) in
  let _, s2 = store_blocks_inner #w st j () in
  assert (res.[i] == (uints_to_bytes_le (vec_v st.[j])).[i % (w * 4)]);
  index_uints_to_bytes_le (vec_v st.[j]) (i % (w * 4));

  assert (res.[i] == (uint_to_bytes_le (vec_v st.[j]).[(i % (w * 4)) / 4]).[(i % (w * 4)) % 4]);
  FStar.Math.Lemmas.modulo_modulo_lemma i 4 w;
  assert (res.[i] == (uint_to_bytes_le (vec_v st.[j]).[(i % (w * 4)) / 4]).[i % 4]);
  FStar.Math.Lemmas.modulo_division_lemma i 4 w


val xor_block_scalar_lemma_index:
    k:Scalar.state
  -> b:Scalar.block
  -> i:nat{i < size_block} ->
  Lemma
  (let j = i / 4 in
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


val xor_block_lemma_aux1: i:nat ->
  Lemma (i / size_block * size_block + 4 * ((i % size_block) / 4) == 4 * (i / 4))
let xor_block_lemma_aux1 i = ()

val xor_block_lemma_aux2: i:nat ->
  Lemma (i / size_block * size_block + 4 * ((i % size_block) / 4 + 1) == 4 * (i / 4 + 1))
let xor_block_lemma_aux2 i = xor_block_lemma_aux1 i


val xor_block_scalar_lemma_index_aux:
    #w:lanes
  -> k:state w
  -> b:blocks w
  -> i:nat{i < w * size_block} ->
  Lemma
  (let j = i / 4 in
   (Scalar.xor_block (transpose_state k).[i / size_block] (sub b (i / size_block * size_block) size_block)).[i % size_block] ==
   (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. ((transpose_state k).[i / size_block]).[j % 16])).[i % 4])
let xor_block_scalar_lemma_index_aux #w k b i =
  let j = i / size_block in
  let j1 = i % size_block in
  let j2 = j1 / 4 in

  let b_j = sub b (j * size_block) size_block in
  let res = Scalar.xor_block (transpose_state k).[j] b_j in
  xor_block_scalar_lemma_index (transpose_state k).[j] b_j j1;
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b_j (4 * j2) 4)) ^. ((transpose_state k).[j]).[j2])).[j1 % 4]);

  xor_block_lemma_aux1 i;
  xor_block_lemma_aux2 i;
  FStar.Seq.Properties.slice_slice b (j * size_block) ((j + 1) * size_block) (4 * j2) (4 * (j2 + 1));
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * (i / 4)) 4)) ^. ((transpose_state k).[j]).[j2])).[j1 % 4]);
  FStar.Math.Lemmas.modulo_division_lemma i 4 16;
  FStar.Math.Lemmas.modulo_modulo_lemma i 4 16;
  assert (res.[j1] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * (i / 4)) 4)) ^. ((transpose_state k).[j]).[i / 4 % 16])).[i % 4])


val xor_block_lemma_index:
    #w:lanes
  -> k:state w
  -> b:blocks w
  -> i:nat{i < w * size_block} ->
  Lemma
  ((xor_block k b).[i] ==
   (Scalar.xor_block (transpose_state k).[i / size_block] (sub b (i / size_block * size_block) size_block)).[i % size_block])
let xor_block_lemma_index #w k b i =
  let ib = load_blocks b in
  let kb = transpose k in
  let ob = map2 (^|) ib kb in
  let res = store_blocks ob in
  store_blocks_lemma_index #w ob i;
  let j = i / 4 in
  assert (res.[i] == (uint_to_bytes_le (vec_v ob.[j / w]).[j % w]).[i % 4]);
  assert (vec_v ob.[j / w] == vec_v (ib.[j / w] ^| kb.[j / w]));
  assert ((vec_v ob.[j / w]).[j % w] == (vec_v ib.[j / w]).[j % w] ^. (vec_v kb.[j / w]).[j % w]);
  load_blocks_lemma_index #w b j;
  assert ((vec_v ib.[j / w]).[j % w] == uint_from_bytes_le (sub b (4 * j) 4));
  assert ((vec_v ob.[j / w]).[j % w] == uint_from_bytes_le (sub b (4 * j) 4) ^. (vec_v kb.[j / w]).[j % w]);
  assert (res.[i] == (uint_to_bytes_le (uint_from_bytes_le (sub b (4 * j) 4) ^. (vec_v kb.[j / w]).[j % w])).[i % 4]);
  Lemmas.transpose_lemma_index #w k j;
  FStar.Math.Lemmas.division_multiplication_lemma i 4 16;
  assert (j / 16 == i / 64);
  assert (res.[i] == (uint_to_bytes_le (uint_from_bytes_le (sub b (4 * j) 4) ^. ((transpose_state k).[i / 64]).[j % 16])).[i % 4]);
  let res1 = Scalar.xor_block (transpose_state k).[i / size_block] (sub b (i / size_block * size_block) size_block) in
  xor_block_scalar_lemma_index_aux #w k b i;
  assert (res1.[i % size_block] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. ((transpose_state k).[i / size_block]).[j % 16])).[i % 4]);
  assert (res.[i] == res1.[i % size_block])


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
  (requires
    (forall (j:nat). j < 16 /\ j <> 12 ==> st1.[j] == st2.[j] /\
    st1.[12] == u32 ctr0 /\ st2.[12] == u32 (ctr0 + i)))
  (ensures
    Scalar.chacha20_core (w * incr + i) st1 `Seq.equal` Scalar.chacha20_core (w * incr) st2)
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
  -> incr:counter{w * incr <= max_size_t /\ ctr0 + w <= max_size_t}
  -> b_i:Scalar.block
  -> i:nat{i < w} ->
  Lemma
  (let st0 = chacha20_init #w k n ctr0 in
   let ctx = Scalar.chacha20_init k n ctr0 in
   Scalar.chacha20_encrypt_block ctx (w * incr + i) b_i `Seq.equal`
   Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr) b_i)
let chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 incr b i =
  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  chacha20_init_lemma_i #w k n ctr0 i;
  assert ((transpose_state st0).[i] == Scalar.chacha20_init k n (ctr0 + i));
  chacha20_init_equiv_lemma k n ctr0;
  chacha20_init_equiv_lemma k n (ctr0 + i);
  let st_s = (transpose_state st0).[i] in
  assert (st_s.[12] == u32 (ctr0 + i));
  assert (ctx.[12] == u32 ctr0);
  assert (forall (j:nat). j < 16 /\ j <> 12 ==> ctx.[j] == st_s.[j]);
  chacha20_core_equiv_lemma ctr0 ctx st_s w incr i

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --using_facts_from '-* +Prims +FStar.Math.Lemmas +FStar.Seq +Lib.IntTypes +Lib.Sequence'"

let get_block_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (i:nat{i < (len / blocksize) * blocksize}) :
  Pure (lseq a blocksize) True (fun _ -> i / blocksize < len / blocksize)
=
  div_mul_lt blocksize i (len / blocksize);
  let j: block len blocksize = i / blocksize in
  let b: lseq a blocksize = Seq.slice inp (j * blocksize) ((j + 1) * blocksize) in
  b


let get_last_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len}) :
  Tot (lseq a (len % blocksize))
=
  let rem = len % blocksize in
  let b: lseq a rem = Seq.slice inp (len - rem) len in
  b


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
val lemma_i_div_bs: w:pos -> bs:pos -> bs_v:pos{bs_v == w * bs} -> i:nat ->
  Lemma (w * (i / bs_v) + i % bs_v / bs == i / bs)
let lemma_i_div_bs w bs bs_v i =
  calc (==) {
    w * (i / bs_v) + i % bs_v / bs;
  (==) { (* hyp *) }
    w * (i / bs_v) + i % (w * bs) / bs;
  (==) { FStar.Math.Lemmas.swap_mul w bs }
    w * (i / bs_v) + i % (bs * w) / bs;
  (==) { FStar.Math.Lemmas.modulo_division_lemma i bs w }
    w * (i / bs_v) + i / bs % w;
  (==) { FStar.Math.Lemmas.division_multiplication_lemma i bs w }
    w * ((i / bs) / w) + i / bs % w;
  (==) { FStar.Math.Lemmas.euclidean_division_definition (i / bs) w }
    i / bs;
  }


val lemma_i_div_bs1: w:pos -> bs:pos -> bs_v:pos{bs_v == w * bs} -> len:nat -> i:nat{len / bs_v * bs_v <= i /\ i < len} ->
  Lemma (w * (len / bs_v) + i % bs_v / bs == i / bs)
let lemma_i_div_bs1 w bs bs_v len i =
  div_interval bs_v (len / bs_v) i;
  lemma_i_div_bs w bs bs_v i


val lemma_i_div_bs2: w:pos -> bs:pos -> bs_v:pos{bs_v == w * bs} -> len:nat -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (w * (len / bs_v) + i % bs_v / bs == len / bs)
let lemma_i_div_bs2 w bs bs_v len i =
  div_interval bs (len / bs) i;
  assert (i / bs == len / bs);
  div_mul_l i len w bs;
  assert (i / bs_v == len / bs_v);
  lemma_i_div_bs w bs bs_v i


val lemma_slice_slice_f_vec_f_aux1: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs} -> i:nat ->
  Lemma (i / bs_v * bs_v + i % bs_v / bs * bs == i / bs * bs)
let lemma_slice_slice_f_vec_f_aux1 w bs bs_v i =
  FStar.Math.Lemmas.distributivity_add_left (i / bs_v * w) ((i % bs_v) / bs) bs;
  lemma_i_div_bs w bs bs_v i


val lemma_slice_slice_f_vec_f_aux2: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs} -> i:nat ->
  Lemma (i / bs_v * bs_v + (i % bs_v / bs + 1) * bs == (i / bs + 1) * bs)
let lemma_slice_slice_f_vec_f_aux2 w bs bs_v i =
  lemma_slice_slice_f_vec_f_aux1 w bs bs_v i


val lemma_slice_slice_f_vec_f_aux3: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs} -> i:nat ->
  Lemma ((i % bs_v / bs + 1) * bs <= bs_v)
let lemma_slice_slice_f_vec_f_aux3 w bs bs_v i =
  FStar.Math.Lemmas.modulo_division_lemma i bs w


val lemma_slice_slice_f_vec_f_aux4: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{i < len / bs_v * bs_v} ->
  Lemma ((i / bs_v + 1) * bs_v <= len)
let lemma_slice_slice_f_vec_f_aux4 w bs bs_v len i =
  div_mul_lt bs_v i (len / bs_v)


val lemma_slice_slice_g_vec_f_aux1: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{len / bs_v * bs_v <= i /\ i < len / bs * bs} ->
  Lemma (len - len % bs_v + i % bs_v / bs * bs == i / bs * bs)
let lemma_slice_slice_g_vec_f_aux1 w bs bs_v len i =
  calc (==) {
    len - len % bs_v + i % bs_v / bs * bs;
    (==) { assert (len - len % bs_v == len / bs_v * bs_v) }
    len / bs_v * bs_v + i % bs_v / bs * bs;
    (==) {
      FStar.Math.Lemmas.paren_mul_right (len / bs_v) w bs;
      FStar.Math.Lemmas.distributivity_add_left (len / bs_v * w) ((i % bs_v) / bs) bs }
    (len / bs_v * w + i % bs_v / bs) * bs;
    (==) { lemma_i_div_bs1 w bs bs_v len i }
    i / bs * bs;
  }


val lemma_slice_slice_g_vec_f_aux2: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{len / bs_v * bs_v <= i /\ i < len / bs * bs} ->
  Lemma (len - len % bs_v + (i % bs_v / bs + 1) * bs == (i / bs + 1) * bs)
let lemma_slice_slice_g_vec_f_aux2 w bs bs_v len i =
  FStar.Math.Lemmas.distributivity_add_left (i % bs_v / bs) 1 bs;
  lemma_slice_slice_g_vec_f_aux1 w bs bs_v len i;
  FStar.Math.Lemmas.distributivity_add_left (i / bs) 1 bs


val lemma_slice_slice_g_vec_f_aux3: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{len / bs_v * bs_v <= i /\ i < len / bs * bs} ->
  Lemma ((i % bs_v / bs + 1) * bs <= len % bs_v)
let lemma_slice_slice_g_vec_f_aux3 w bs bs_v len i =
  FStar.Math.Lemmas.distributivity_add_left (i % bs_v / bs) 1 bs;
  lemma_slice_slice_g_vec_f_aux1 w bs bs_v len i;
  assert (len - len % bs_v + i % bs_v / bs * bs + bs == i / bs * bs + bs);
  assert (i % bs_v / bs * bs + bs == i / bs * bs + bs - len + len % bs_v);
  div_mul_lt bs i (len / bs);
  assert ((i / bs + 1) * bs <= len)


val lemma_slice_slice_g_vec_f_aux4: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{len / bs_v * bs_v <= i /\ i < len / bs * bs} ->
  Lemma (i % bs_v < (len % bs_v) / bs * bs)
let lemma_slice_slice_g_vec_f_aux4 w bs bs_v len i =
  lemma_slice_slice_f_vec_f_aux1 w bs bs_v len;
  assert ((len / bs_v) * bs_v + (len % bs_v) / bs * bs == len / bs * bs);

  div_interval bs_v (len / bs_v) i;
  assert (i / bs_v == len / bs_v);
  assert ((i / bs_v) * bs_v + (len % bs_v) / bs * bs == len / bs * bs);
  FStar.Math.Lemmas.euclidean_division_definition i bs_v;
  assert (i - i % bs_v + (len % bs_v) / bs * bs == len / bs * bs);
  assert (i - len / bs * bs + (len % bs_v) / bs * bs == i % bs_v)


val lemma_slice_slice_g_vec_g_aux: w:pos -> bs:pos -> bs_v:nat{bs_v == w * bs}
  -> len:nat -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma ((len % bs_v) / bs * bs <= i % bs_v)
let lemma_slice_slice_g_vec_g_aux w bs bs_v len i =
  lemma_slice_slice_f_vec_f_aux1 w bs bs_v len;
  assert ((len / bs_v) * bs_v + (len % bs_v) / bs * bs == len / bs * bs);

  div_interval bs (len / bs) i;
  assert (i / bs == len / bs);
  div_mul_l i len w bs;
  assert (i / bs_v == len / bs_v);
  assert ((i / bs_v) * bs_v + (len % bs_v) / bs * bs == len / bs * bs);
  FStar.Math.Lemmas.euclidean_division_definition i bs_v;
  assert (i - i % bs_v + (len % bs_v) / bs * bs == len / bs * bs);
  assert (i - len / bs * bs + (len % bs_v) / bs * bs == i % bs_v)


#set-options "--max_ifuel 0"

val chacha20_encrypt_block_lemma_index:
    #w:lanes
  -> st0:state w
  -> j_v:counter{w * j_v <= max_size_t}
  -> b_v:blocks w
  -> j:nat{j < w * size_block} ->
  Lemma
  (let b = get_block_s #uint8 #(w * size_block) size_block b_v j in
   (chacha20_encrypt_block st0 j_v b_v).[j] ==
   (Scalar.chacha20_encrypt_block (transpose_state st0).[j / size_block] (w * j_v) b).[j % size_block])

let chacha20_encrypt_block_lemma_index #w st0 j_v b_v j =
  let k = chacha20_core j_v st0 in
  chacha20_core_lemma_i #w j_v st0 (j / size_block);
  let res = xor_block k b_v in
  xor_block_lemma_index #w k b_v j


val chacha20_encrypt_block_equiv_lemma_index:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> j_v:counter{w * j_v <= max_size_t}
  -> b_v:blocks w
  -> j:nat{j < w * size_block} ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in
   let b = get_block_s #uint8 #(w * size_block) size_block b_v j in
   (chacha20_encrypt_block st_v0 j_v b_v).[j] ==
   (Scalar.chacha20_encrypt_block st0 (w * j_v + j / size_block) b).[j % size_block])

let chacha20_encrypt_block_equiv_lemma_index #w k n ctr0 j_v b_v j =
  let st_v0 = chacha20_init #w k n ctr0 in
  let st0 = Scalar.chacha20_init k n ctr0 in
  let b = get_block_s #uint8 #(w * size_block) size_block b_v j in
  chacha20_encrypt_block_lemma_index #w st_v0 j_v b_v j;
  chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 j_v b (j / size_block)


val chacha20_encrypt_block_equiv_lemma_index1:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> b_v:blocks w
  -> i:size_nat ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in
   let b = get_block_s #uint8 #(w * size_block) size_block b_v (i % (w * size_block)) in
   (chacha20_encrypt_block st_v0 (i / (w * size_block)) b_v).[i % (w * size_block)] ==
   (Scalar.chacha20_encrypt_block st0 (i / size_block) b).[i % size_block])

let chacha20_encrypt_block_equiv_lemma_index1 #w k n ctr0 b_v i =
  let st_v0 = chacha20_init #w k n ctr0 in
  let st0 = Scalar.chacha20_init k n ctr0 in

  let bs_v = w * size_block in
  let j_v = i / bs_v in
  let j = i % bs_v in

  let b = get_block_s #uint8 #(w * size_block) size_block b_v j in
  chacha20_encrypt_block_equiv_lemma_index #w k n ctr0 j_v b_v j;
  lemma_i_div_bs w size_block bs_v i;
  FStar.Math.Lemmas.modulo_modulo_lemma i size_block w


val chacha20_encrypt_last_equiv_lemma_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> incr:counter{w * incr <= max_size_t}
  -> len:size_nat{len < size_block}
  -> b_i:lbytes len
  -> i:size_nat{i < w} ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in
   Scalar.chacha20_encrypt_last st0 (w * incr + i) len b_i `Seq.equal`
   Scalar.chacha20_encrypt_last (transpose_state st_v0).[i] (w * incr) len b_i)

let chacha20_encrypt_last_equiv_lemma_i #w k n ctr0 incr len b i =
  let plain = create size_block (u8 0) in
  let plain = update_sub plain 0 len b in
  chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 incr plain i


val chacha20_encrypt_last_lemma_index_aux:
    #w:lanes
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len ->
  Lemma
  (let bs = size_block in
   let nb = len / bs in
   let last = Seq.slice b (nb * bs) len in
   let plain1 = create bs (u8 0) in
   let plain1 = update_sub plain1 0 (len % bs) last in

   let plain = create (w*bs) (u8 0) in
   let plain = update_sub plain 0 len b in
   let last_plain = Seq.slice plain (nb*bs) ((nb+1)*bs) in
   plain1 `Seq.equal` last_plain)

let chacha20_encrypt_last_lemma_index_aux #w len b =
  let bs = size_block in
  let nb = len / bs in
  let rem = len % bs in
  let last = Seq.slice b (nb * bs) len in

  let plain1 = create bs (u8 0) in
  let plain1 = update_sub plain1 0 (len % bs) last in
  let zeroes1 = create (bs - rem) (u8 0) in
  FStar.Seq.Properties.lemma_split plain1 rem;
  FStar.Seq.Properties.lemma_split (Seq.append last zeroes1) rem;
  eq_intro plain1 (concat #uint8 #rem #(bs - rem) last zeroes1);
  assert (plain1 == Seq.append last zeroes1);

  let plain = create (w*bs) (u8 0) in
  let plain = update_sub plain 0 len b in
  let zeroes2 = create (w*bs - len) (u8 0) in
  FStar.Seq.Properties.lemma_split plain len;
  FStar.Seq.Properties.lemma_split (Seq.append b zeroes2) len;
  eq_intro plain (Seq.append b zeroes2);
  assert (plain == Seq.append b zeroes2);

  let last_plain = Seq.slice plain (nb*bs) ((nb+1)*bs) in
  FStar.Seq.Properties.lemma_split last_plain rem;
  eq_intro plain1 last_plain


#set-options "--z3rlimit 150"

val chacha20_encrypt_last_lemma_index:
    #w:lanes
  -> st0:state w
  -> incr:counter{w * incr <= max_size_t}
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len
  -> j:size_nat{j < len} ->
  Lemma
  (if j < len / size_block * size_block then begin
    let b_j = get_block_s #uint8 #len size_block b j in
    (chacha20_encrypt_last st0 incr len b).[j] ==
    (Scalar.chacha20_encrypt_block (transpose_state st0).[j / size_block] (w * incr) b_j).[j % size_block] end
   else begin
    let last = get_last_s size_block b in
    //mod_div_lt size_block j len;
    (chacha20_encrypt_last st0 incr len b).[j] ==
    (Scalar.chacha20_encrypt_last (transpose_state st0).[len / size_block] (w * incr) (len % size_block) last).[j % size_block] end)

let chacha20_encrypt_last_lemma_index #w st0 incr len b j =
  let bs = size_block in
  let bs_v = w * bs in
  let plain = create bs_v (u8 0) in
  let plain = update_sub plain 0 len b in
  let res = chacha20_encrypt_last st0 incr len b in
  assert (res == Seq.slice (chacha20_encrypt_block st0 incr plain) 0 len);
  chacha20_encrypt_block_lemma_index #w st0 incr plain j;
  let b_j = get_block_s #uint8 #bs_v bs plain j in
  assert ((chacha20_encrypt_block st0 incr plain).[j] ==
    (Scalar.chacha20_encrypt_block (transpose_state st0).[j / bs] (w * incr) b_j).[j % bs]);

  if j < len / bs * bs then begin
    let b_j = get_block_s #uint8 #len bs b j in
    assert ((chacha20_encrypt_last st0 incr len b).[j] ==
      (Scalar.chacha20_encrypt_block (transpose_state st0).[j / bs] (w * incr) b_j).[j % bs]) end
  else begin
    let nb = len / bs in
    let last_plain = Seq.slice plain (nb*size_block) ((nb+1)*size_block) in
    let last = get_last_s bs b in
    let plain1 = create bs (u8 0) in
    let plain1 = update_sub plain1 0 (len % bs) last in
    chacha20_encrypt_last_lemma_index_aux #w len b;
    assert (plain1 == last_plain);
    assert ((chacha20_encrypt_last st0 incr len b).[j] ==
    (Scalar.chacha20_encrypt_last (transpose_state st0).[len / bs] (w * incr) (len % bs) last).[j % bs]) end


val chacha20_encrypt_last_equiv_lemma_index:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> incr:counter{w * incr <= max_size_t}
  -> len:size_nat{len < w * size_block}
  -> b:lbytes len
  -> j:size_nat{j < len} ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in

   if j < len / size_block * size_block then begin
     let b_j = get_block_s #uint8 #len size_block b j in
     (chacha20_encrypt_last st_v0 incr len b).[j] ==
     (Scalar.chacha20_encrypt_block st0 (w * incr + j / size_block) b_j).[j % size_block] end
   else begin
     let last = get_last_s #uint8 #len size_block b in
     (chacha20_encrypt_last st_v0 incr len b).[j] ==
     (Scalar.chacha20_encrypt_last st0 (w * incr + len / size_block) (len % size_block) last).[j % size_block] end)

let chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 incr len b j =
  let st0 = chacha20_init #w k n ctr0 in
  let ctx = Scalar.chacha20_init k n ctr0 in
  chacha20_encrypt_last_lemma_index #w st0 incr len b j;
  let bs = size_block in
  if j < len / bs * bs then begin
    let b_j = get_block_s #uint8 #len size_block b j in
    chacha20_encrypt_block_equiv_lemma_i #w k n ctr0 incr b_j (j / bs) end
  else begin
    let last = get_last_s #uint8 #len size_block b in
    chacha20_encrypt_last_equiv_lemma_i #w k n ctr0 incr (len % bs) last (len / bs) end


val chacha20_encrypt_last_equiv_lemma_index1:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> len:size_nat
  -> rem:size_nat{rem == len % (w * size_block)}
  -> b_v:lbytes rem
  -> bs_v:size_nat{bs_v == w * size_block}
  -> i:size_nat{i % bs_v < rem / size_block * size_block /\ len / bs_v * bs_v <= i /\ i < len} ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in
   let bs_v = w * size_block in
   let j = i % bs_v in

   let b_j = get_block_s #uint8 #rem size_block b_v j in
   (chacha20_encrypt_last st_v0 (len / bs_v) rem b_v).[j] ==
   (Scalar.chacha20_encrypt_block st0 (i / size_block) b_j).[i % size_block])

let chacha20_encrypt_last_equiv_lemma_index1 #w k n ctr0 len rem b_v bs_v i =
  let st_v0 = chacha20_init #w k n ctr0 in
  let st0 = Scalar.chacha20_init k n ctr0 in
  let bs = size_block in
  let bs_v = w * bs in
  let j = i % bs_v in
  chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 (len / bs_v) rem b_v j;
  lemma_i_div_bs1 w bs bs_v len i;
  FStar.Math.Lemmas.modulo_modulo_lemma i size_block w


#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val chacha20_encrypt_last_equiv_lemma_index2:
    #w:lanes
  -> k:key
  -> n:nonce
  -> ctr0:counter{ctr0 + w <= max_size_t}
  -> len:size_nat
  -> rem:size_nat{rem == len % (w * size_block)}
  -> b_v:lbytes rem
  -> bs_v:size_nat{bs_v == w * size_block}
  -> i:size_nat{rem / size_block * size_block <= i % bs_v /\ i % bs_v < rem /\ len / size_block * size_block <= i /\ i < len} ->
  Lemma
  (let st_v0 = chacha20_init #w k n ctr0 in
   let st0 = Scalar.chacha20_init k n ctr0 in
   let (j:nat{j < rem}) = i % bs_v in
   let b_j: lseq uint8 (rem % size_block) = get_last_s #uint8 #rem size_block b_v in
   FStar.Math.Lemmas.modulo_modulo_lemma i size_block w;
   (chacha20_encrypt_last st_v0 (len / bs_v) rem b_v).[j] ==
   (Scalar.chacha20_encrypt_last st0 (len / size_block) (rem % size_block) b_j).[i % size_block])
#pop-options

#push-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"
let chacha20_encrypt_last_equiv_lemma_index2 #w k n ctr0 len rem b_v bs_v i =
  let st_v0 = chacha20_init #w k n ctr0 in
  let st0 = Scalar.chacha20_init k n ctr0 in
  let j = i % bs_v in
  chacha20_encrypt_last_equiv_lemma_index #w k n ctr0 (len / bs_v) rem b_v j;
  lemma_i_div_bs2 w size_block bs_v len i;
  FStar.Math.Lemmas.modulo_modulo_lemma i size_block w

#pop-options

val lemma_slice_slice_f_vec_f:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len}
  -> i:nat{i < len / (w * bs) * (w * bs) /\ i < len / bs * bs} ->
  Lemma
  (let bs_v = w * bs in
   let b_v = get_block_s #a #len bs_v inp i in
   let b = get_block_s #a #len bs inp i in
   FStar.Math.Lemmas.cancel_mul_div w bs;
   //assert (i % bs_v < bs_v / bs * bs);
   let b1 = get_block_s #a #bs_v bs b_v (i % bs_v) in
   b1 `Seq.equal` b)

let lemma_slice_slice_f_vec_f #a #len w bs inp i =
  let bs_v = w * bs in
  let j_v = i / bs_v in
  let i1 = i % bs_v in
  let j = i1 / bs in

  lemma_slice_slice_f_vec_f_aux4 w bs bs_v len i;
  //assert ((j_v + 1) * bs_v <= len);
  lemma_slice_slice_f_vec_f_aux3 w bs bs_v i;
  //assert ((j + 1) * bs <= bs_v);
  Seq.slice_slice inp (j_v * bs_v) ((j_v + 1) * bs_v) (j * bs) ((j + 1) * bs);
  lemma_slice_slice_f_vec_f_aux1 w bs bs_v i;
  //assert (j_v * bs_v + j * bs == i / bs * bs);
  lemma_slice_slice_f_vec_f_aux2 w bs bs_v i
  //assert (j_v * bs_v + (j + 1) * bs == (i / bs + 1) * bs)


val lemma_slice_slice_g_vec_f:
    #a:Type
 -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len}
  -> i:nat{len / (w * bs) * (w * bs) <= i /\ i < len / bs * bs} ->
  Lemma
  (let bs_v = w * bs in
   let rem = len % bs_v in
   let b_v: lseq a rem = get_last_s #a #len bs_v inp in
   let b: lseq a bs = get_block_s #a #len bs inp i in
   lemma_slice_slice_g_vec_f_aux4 w bs bs_v len i;
   let b1: lseq a bs = get_block_s #a #rem bs b_v (i % bs_v) in
   b1 `Seq.equal` b)

let lemma_slice_slice_g_vec_f #a #len w bs inp i =
  let bs_v = w * bs in
  let rem = len % bs_v in
  let i1 = i % bs_v in
  let j = i1 / bs in
  lemma_slice_slice_g_vec_f_aux3 w bs bs_v len i;
  assert ((j + 1) * bs <= rem);
  Seq.slice_slice inp (len - rem) len (j * bs) ((j + 1) * bs);
  lemma_slice_slice_g_vec_f_aux1 w bs bs_v len i;
  assert (len - rem + j * bs == i / bs * bs);
  lemma_slice_slice_g_vec_f_aux2 w bs bs_v len i;
  assert (len - rem + (j + 1) * bs == (i / bs + 1) * bs)


val lemma_slice_slice_g_vec_g:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len} ->
  Lemma
  (let bs_v = w * bs in
   let rem = len % bs_v in
   let b_v = get_last_s #a #len bs_v inp in
   let b = get_last_s #a #len bs inp in
   let b1 = get_last_s #a #rem bs b_v in
   b1 `Seq.equal` b)

let lemma_slice_slice_g_vec_g #a #len w bs inp =
  let bs_v = w * bs in
  let rem = len % bs_v in
  Seq.slice_slice inp (len - rem) len (rem - rem % bs) rem;
  FStar.Math.Lemmas.modulo_modulo_lemma len bs w;
  FStar.Math.Lemmas.swap_mul w bs;
  assert (len % bs == rem % bs)


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

val chacha20_vec_equiv_pre:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t}
  -> i:nat{i < length msg} -> prop

let chacha20_vec_equiv_pre #w key nonce ctr0 msg i =
  let st_v0 = chacha20_init #w key nonce ctr0 in
  let st0 = Scalar.chacha20_init key nonce ctr0 in

  let f_v = chacha20_encrypt_block st_v0 in
  let g_v = chacha20_encrypt_last st_v0 in

  let f = Scalar.chacha20_encrypt_block st0 in
  let g = Scalar.chacha20_encrypt_last st0 in
  map_blocks_vec_equiv_pre #uint8 w size_block msg f g f_v g_v i


val lemma_chacha20_vec_equiv_pre_f_vec_f:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t}
  -> i:size_nat{i < length msg / size_block * size_block /\ i < length msg / (w * size_block) * (w * size_block)} ->
  Lemma (chacha20_vec_equiv_pre #w k n c msg i)

let lemma_chacha20_vec_equiv_pre_f_vec_f #w key nonce ctr0 msg i =
  let len = length msg in
  let bs = size_block in
  let bs_v = w * bs in

  let b_v = get_block_s #uint8 #len bs_v msg i in
  chacha20_encrypt_block_equiv_lemma_index1 #w key nonce ctr0 b_v i;
  lemma_slice_slice_f_vec_f #uint8 #len w size_block msg i


val lemma_chacha20_vec_equiv_pre_g_vec_f:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t}
  -> i:nat{length msg / (w * size_block) * (w * size_block) <= i /\ i < length msg / size_block * size_block} ->
  Lemma (chacha20_vec_equiv_pre #w k n c msg i)

let lemma_chacha20_vec_equiv_pre_g_vec_f #w key nonce ctr0 msg i =
  let len = length msg in
  let bs = size_block in
  let bs_v = w * bs in

  let b_v = get_last_s #uint8 #len bs_v msg in
  lemma_slice_slice_g_vec_f_aux4 w bs bs_v len i;
  assert (i % bs_v < (len % bs_v) / bs * bs);
  chacha20_encrypt_last_equiv_lemma_index1 #w key nonce ctr0 len (len % bs_v) b_v bs_v i;
  lemma_slice_slice_g_vec_f #uint8 #len w bs msg i


val lemma_chacha20_vec_equiv_pre_g_vec_g:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t}
  -> i:nat{length msg / size_block * size_block <= i /\ i < length msg} ->
  Lemma (chacha20_vec_equiv_pre #w k n c msg i)

let lemma_chacha20_vec_equiv_pre_g_vec_g #w key nonce ctr0 msg i =
  let len = length msg in
  let bs = size_block in
  let bs_v = w * bs in

  let b_v = get_last_s #uint8 #len bs_v msg in
  let rem = len % bs_v in
  mod_div_lt bs_v i len;
  assert (i % bs_v < rem);
  lemma_slice_slice_g_vec_g_aux w bs bs_v len i;
  assert (rem / bs * bs <= i % bs_v);
  chacha20_encrypt_last_equiv_lemma_index2 #w key nonce ctr0 len rem b_v bs_v i;
  lemma_slice_slice_g_vec_g #uint8 #len w bs msg


val lemma_chacha20_vec_equiv_pre:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t}
  -> i:nat{i < length msg} ->
  Lemma (chacha20_vec_equiv_pre #w k n c msg i)

let lemma_chacha20_vec_equiv_pre #w key nonce ctr0 msg i =
  let len = length msg in
  let blocksize = size_block in
  let blocksize_v = w * blocksize in

  if i < (len / blocksize) * blocksize then
    begin
    if i < (len / blocksize_v) * blocksize_v then
      lemma_chacha20_vec_equiv_pre_f_vec_f #w key nonce ctr0 msg i
    else
      lemma_chacha20_vec_equiv_pre_g_vec_f #w key nonce ctr0 msg i
    end
  else
    lemma_chacha20_vec_equiv_pre_g_vec_g #w key nonce ctr0 msg i


val lemma_chacha20_vec_equiv:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c:counter
  -> msg:seq uint8{length msg <= max_size_t /\ c + w <= max_size_t} ->
  Lemma (chacha20_encrypt_bytes #w k n c msg `Seq.equal` Scalar.chacha20_encrypt_bytes k n c msg)

let lemma_chacha20_vec_equiv #w key nonce ctr0 msg =
  let st_v0 = chacha20_init #w key nonce ctr0 in
  let st0 = Scalar.chacha20_init key nonce ctr0 in

  let f_v = chacha20_encrypt_block st_v0 in
  let g_v = chacha20_encrypt_last st_v0 in

  let f = Scalar.chacha20_encrypt_block st0 in
  let g = Scalar.chacha20_encrypt_last st0 in

  Classical.forall_intro (lemma_chacha20_vec_equiv_pre #w key nonce ctr0 msg);
  lemma_map_blocks_vec #uint8 w size_block msg f g f_v g_v
