module Hacl.Spec.Chacha20.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Scalar = Spec.Chacha20
module Lemmas = Hacl.Spec.Chacha20.Lemmas
module VecLemmas = Lib.Vec.Lemmas
module SeqLemmas = Lib.Sequence.Lemmas

open Hacl.Spec.Chacha20.Vec


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let blocksize = size_block

///
///  Scalar-related lemmas
///

val chacha20_init_scalar_lemma: k:key -> n:nonce -> c0:counter -> Lemma
  (let uc = map secret chacha20_constants in
   let uk = uints_from_bytes_le #U32 #SEC #8 k in
   let uctr = create 1 (u32 c0) in
   let un = uints_from_bytes_le #U32 #SEC #3 n in
   Scalar.chacha20_init k n c0 == uc @| uk @| uctr @| un)

let chacha20_init_scalar_lemma k n c0 =
  let uc = map secret chacha20_constants in
  let uk = uints_from_bytes_le #U32 #SEC #8 k in
  let uctr = create 1 (u32 c0) in
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
  let st = st.[12] <- u32 c0 in
  eq_intro (sub st 0 4) uc;
  eq_intro (sub st 4 8) uk;
  let res1 = update_sub st 13 3 (uints_from_bytes_le #U32 #SEC #3 n) in
  eq_intro (sub res1 0 4) uc;
  eq_intro (sub res1 4 8) uk;
  eq_intro (sub res1 12 1) uctr;
  eq_intro (sub res1 13 3) un;

  Seq.Properties.lemma_split (sub res 0 (len0 + len1)) len0;
  Seq.Properties.lemma_split (sub res1 0 (len0 + len1)) len0;

  Seq.Properties.lemma_split (sub res 0 (len0 + len1 + len2)) (len0 + len1);
  Seq.Properties.lemma_split (sub res1 0 (len0 + len1 + len2)) (len0 + len1);

  Seq.Properties.lemma_split res (len0 + len1 + len2);
  Seq.Properties.lemma_split res1 (len0 + len1 + len2)


val add_counter_lemma_aux:
    w:lanes
  -> c0:counter
  -> c:counter{w * c <= max_size_t /\ c0 + w <= max_size_t}
  -> i:nat{i < w}
  -> b:uint32 ->
  Lemma (b +. u32 c0 +. u32 (w * c + i) == b +. u32 (c0 + i) +. u32 (w * c))

let add_counter_lemma_aux w c0 c i b =
  let lp = b +. u32 c0 +. u32 (w * c + i) in
  let rp = b +. u32 (c0 + i) +. u32 (w * c) in
  assert (v lp == ((v b + c0) % modulus U32 + (w * c + i)) % modulus U32);
  assert (v rp == ((v b + c0 + i) % modulus U32 + (w * c)) % modulus U32);
  Math.Lemmas.lemma_mod_plus_distr_l (v b + c0) (w * c + i) (modulus U32);
  Math.Lemmas.lemma_mod_plus_distr_l (v b + c0 + i) (w * c) (modulus U32)


val chacha20_core_scalar_lemma:
    w:lanes
  -> st1:Scalar.state
  -> st2:Scalar.state
  -> c0:counter
  -> c:counter{w * c <= max_size_t /\ c0 + w <= max_size_t}
  -> i:nat{i < w} -> Lemma
  (requires
    (forall (j:nat). j < 16 /\ j <> 12 ==> st1.[j] == st2.[j] /\
    st1.[12] == u32 c0 /\ st2.[12] == u32 (c0 + i)))
  (ensures
    Scalar.chacha20_core (w * c + i) st1 `Seq.equal` Scalar.chacha20_core (w * c) st2)

let chacha20_core_scalar_lemma w st1 st2 c0 c i =
  let k1 = Scalar.chacha20_add_counter st1 (w * c + i) in
  assert (k1.[12] == u32 c0 +. u32 (w * c + i));
  let k2 = Scalar.chacha20_add_counter st2 (w * c) in
  assert (k2.[12] == u32 (c0 + i) +. u32 (w * c));
  assert (v k1.[12] == v k2.[12]);
  eq_intro k1 k2;
  let k = Scalar.rounds k1 in
  let k1 = Scalar.sum_state k st1 in
  assert (k1.[12] == k.[12] +. u32 c0);
  let k2 = Scalar.sum_state k st2 in
  assert (k2.[12] == k.[12] +. u32 (c0 + i));
  assert (forall (j:nat). j < 16 /\ j <> 12 ==> k1.[j] == k2.[j]);
  let k1 = Scalar.chacha20_add_counter k1 (w * c + i) in
  assert (k1.[12] == k.[12] +. u32 c0 +. u32 (w * c + i));
  let k2 = Scalar.chacha20_add_counter k2 (w * c) in
  assert (k2.[12] == k.[12] +. u32 (c0 + i) +. u32 (w * c));
  add_counter_lemma_aux w c0 c i k.[12];
  eq_intro k1 k2


val kb_equiv_lemma:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter
  -> c:counter{w * c <= max_size_t /\ c0 + w <= max_size_t}
  -> i:nat{i < w} -> Lemma
  (let st1 = Scalar.chacha20_init k n c0 in
   let st2 = Scalar.chacha20_init k n (c0 + i) in
   Scalar.chacha20_core (w * c + i) st1 `Seq.equal` Scalar.chacha20_core (w * c) st2)

let kb_equiv_lemma #w k n c0 c i =
  let st1 = Scalar.chacha20_init k n c0 in
  let st2 = Scalar.chacha20_init k n (c0 + i) in
  chacha20_init_scalar_lemma k n c0;
  chacha20_init_scalar_lemma k n (c0 + i);
  chacha20_core_scalar_lemma w st1 st2 c0 c i

///
///  Vectorised-related lemmas
///

#set-options "--z3rlimit 200"

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
  Lemma ((transpose_state (quarter_round #w a b c d m)).[i] `Seq.equal`
    Scalar.quarter_round a b c d (transpose_state m).[i])

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
  eq_intro (transpose_state (quarter_round #w a b c d m)).[i]
    (Scalar.quarter_round a b c d (transpose_state m).[i])


val column_round_lemma_i: #w:lanes -> m:state w -> i:nat{i < w} ->
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


val diagonal_round_lemma_i: #w:lanes -> m:state w -> i:nat{i < w} ->
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


val double_round_lemma_i: #w:lanes -> m:state w -> i:nat{i < w} ->
  Lemma ((transpose_state (double_round #w m)).[i] `Seq.equal` Scalar.double_round (transpose_state m).[i])

let double_round_lemma_i #w m i =
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


val rounds_lemma_i: #w:lanes -> m:state w -> i:nat{i < w} ->
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
  double_round_lemma_i #w m i;
  double_round_lemma_i #w m1 i;
  double_round_lemma_i #w m2 i;
  double_round_lemma_i #w m3 i;
  double_round_lemma_i #w m4 i;
  double_round_lemma_i #w m5 i;
  double_round_lemma_i #w m6 i;
  double_round_lemma_i #w m7 i;
  double_round_lemma_i #w m8 i;
  double_round_lemma_i #w m9 i;
  assert ((transpose_state m10).[i] == scalar_rounds ms);
  scalar_rounds_unroll_lemma ms


val sum_state_lemma_i: #w:lanes -> st1:state w -> st2:state w -> i:nat{i < w} ->
  Lemma ((transpose_state (sum_state st1 st2)).[i] `Seq.equal` Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])

let sum_state_lemma_i #w st1 st2 i =
  eq_intro (transpose_state (sum_state st1 st2)).[i] (Scalar.sum_state (transpose_state st1).[i] (transpose_state st2).[i])


val add_counter_lemma_i: #w:lanes -> st:state w -> c:counter{w * c <= max_size_t} -> i:nat{i < w} ->
  Lemma ((transpose_state (add_counter #w c st)).[i] `Seq.equal` Scalar.chacha20_add_counter (transpose_state st).[i] (w * c))

let add_counter_lemma_i #w st c i =
  Math.Lemmas.modulo_lemma (w * c) (pow2 32);
  assert (v (u32 w *! u32 c) == v (u32 (w * c)));
  eq_intro (transpose_state (add_counter #w c st)).[i] (Scalar.chacha20_add_counter (transpose_state st).[i] (w * c))

//kb_v_i
val chacha20_core_lemma_i: #w:lanes -> c:counter{w * c <= max_size_t} -> st_v0:state w -> i:nat{i < w} ->
  Lemma ((transpose_state (chacha20_core c st_v0)).[i] `Seq.equal` Scalar.chacha20_core (w * c) (transpose_state st_v0).[i])

let chacha20_core_lemma_i #w c st_v0 i =
  let k0 = add_counter c st_v0 in
  add_counter_lemma_i st_v0 c i;
  let k1 = rounds k0 in
  rounds_lemma_i k0 i;
  let k2 = sum_state k1 st_v0 in
  sum_state_lemma_i k1 st_v0 i;
  let k3 = add_counter c k2 in
  add_counter_lemma_i k2 c i

//init_v_i
val chacha20_init_lemma_i: #w:lanes -> k:key -> n:nonce -> c0:counter{c0 + w <= max_size_t} -> i:nat{i < w} ->
  Lemma ((transpose_state (chacha20_init #w k n c0)).[i] `Seq.equal` Scalar.chacha20_init k n (c0 + i))

let chacha20_init_lemma_i #w k n c0 i =
  let st1 = setup1 k n c0 in
  assert (st1 == Scalar.chacha20_init k n c0);
  assert (st1.[12] == u32 c0);

  let st = map (vec_load_i w) st1 in
  eq_intro (transpose_state st).[i] st1;
  assert ((transpose_state st).[i] == st1);

  let c = vec_counter U32 w in
  assert ((vec_v c).[i] == u32 i);

  let res = st.[12] <- st.[12] +| c in
  let res1 = st1.[12] <- st1.[12] +. u32 i in
  eq_intro (transpose_state res).[i] res1;
  assert ((transpose_state res).[i] == res1);
  assert (res1.[12] == u32 c0 +. u32 i);
  assert (v (u32 c0 +. u32 i) == v (u32 (c0 + i)));
  assert (res1.[12] == u32 (c0 + i));

  let res2 = Scalar.chacha20_init k n (c0 + i) in
  chacha20_init_scalar_lemma k n c0;
  chacha20_init_scalar_lemma k n (c0 + i);
  eq_intro res1 res2

///
///  XOR-related lemmas
///

val lemma_i_div_w4: w:pos -> i:nat{i < w * blocksize} ->
  Lemma (let bs = w * 4 in i / bs * bs + i % bs / 4 * 4 == i / 4 * 4)
let lemma_i_div_w4 w i =
  let bs = w * 4 in
  calc (==) {
    i / bs * bs + i % bs / 4 * 4;
    (==) { Math.Lemmas.euclidean_division_definition (i % bs) 4 }
    i / bs * bs + i % bs - i % bs % 4;
    (==) { Math.Lemmas.euclidean_division_definition i bs }
    i - i % bs % 4;
    (==) { Math.Lemmas.modulo_modulo_lemma i 4 w }
    i - i % 4;
    (==) { Math.Lemmas.euclidean_division_definition i 4 }
    i / 4 * 4;
    }

val lemma_i_div_blocksize: w:pos -> i:nat{i < w * blocksize} ->
  Lemma (i / blocksize * blocksize + i % blocksize / 4 * 4 == i / 4 * 4)
let lemma_i_div_blocksize w i =
  calc (==) {
    i / blocksize * blocksize + i % blocksize / 4 * 4;
    (==) { Math.Lemmas.euclidean_division_definition (i % blocksize) 4 }
    i / blocksize * blocksize + i % blocksize - i % blocksize % 4;
    (==) { Math.Lemmas.modulo_modulo_lemma i 4 16 }
    i / blocksize * blocksize + i % blocksize - i % 4;
    (==) { Math.Lemmas.euclidean_division_definition i blocksize }
    i - i % 4;
    (==) { Math.Lemmas.euclidean_division_definition i 4 }
    i / 4 * 4;
  }


val xor_block_vec_lemma_i: #w:lanes -> k:state w -> b:blocks w -> i:nat{i < w * blocksize} -> Lemma
  (let bs = w * 4 in
   let j = i / bs in
   let block = sub b (i / 4 * 4) 4 in
   Seq.index (xor_block k b) i ==
   Seq.index (uint_to_bytes_le ((uint_from_bytes_le block) ^. (Seq.index (vec_v k.[j]) (i % bs / 4)))) (i % 4))

let xor_block_vec_lemma_i #w k b i =
  let bs = w * 4 in
  let j = i / bs in
  let kb_j = vec_v k.[j] in

  let b_j = sub b (i / bs * bs) bs in
  let b_i = sub b_j (i % bs / 4 * 4) 4 in
  let block = sub b (i / 4 * 4) 4 in

  let ob = map2 (^.) (uints_from_bytes_le b_j) kb_j in

  calc (==) {
    Seq.index (xor_block k b) i;
    (==) { index_map_blocks_multi (w * 4) 16 16 b (xor_block_f #w k) i }
    Seq.index (uints_to_bytes_le ob) (i % bs);
    (==) { index_uints_to_bytes_le ob (i % bs) }
    Seq.index (uint_to_bytes_le ob.[i % bs / 4]) (i % bs % 4);
    (==) { Math.Lemmas.modulo_modulo_lemma i 4 w }
    Seq.index (uint_to_bytes_le ob.[i % bs / 4]) (i % 4);
    (==) { (* def of xor *) }
    Seq.index (uint_to_bytes_le ((uints_from_bytes_le #U32 #SEC #w b_j).[i % bs / 4] ^. kb_j.[i % bs / 4])) (i % 4);
    (==) { index_uints_from_bytes_le #U32 #SEC #w b_j (i % bs / 4) }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le b_i) ^. kb_j.[i % bs / 4])) (i % 4);
    (==) { lemma_i_div_w4 w i; Seq.slice_slice b (j * bs) (j * bs + bs) (i % bs / 4 * 4) (i % bs / 4 * 4 + 4) }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le block) ^. kb_j.[i % bs / 4])) (i % 4);
    }


val xor_block_scalar_lemma_i: k:Scalar.state -> b:Scalar.block -> i:nat{i < blocksize} -> Lemma
  ((Scalar.xor_block k b).[i] == (uint_to_bytes_le ((uint_from_bytes_le (sub b (i / 4 * 4) 4)) ^. k.[i / 4])).[i % 4])

let xor_block_scalar_lemma_i k b i =
  let ib = uints_from_bytes_le b in
  let ob = map2 (^.) ib k in
  let b_i = sub b (i / 4 * 4) 4 in

  calc (==) {
    Seq.index (uints_to_bytes_le ob) i;
    (==) { index_uints_to_bytes_le ob i }
    Seq.index (uint_to_bytes_le ob.[i / 4]) (i % 4);
    (==) { (* def of xor *) }
    Seq.index (uint_to_bytes_le (ib.[i / 4] ^. k.[i / 4])) (i % 4);
    (==) { index_uints_from_bytes_le #U32 #SEC #16 b (i / 4) }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le b_i) ^. k.[i / 4])) (i % 4);
    }


val transpose_lemma_i: #w:lanes -> k:state w -> i:nat{i < w * blocksize} -> Lemma
  (Seq.index (vec_v (Seq.index (transpose k) (i / (w * 4)))) (i % (w * 4) / 4) ==
   Seq.index (Seq.index (transpose_state k) (i / blocksize)) (i % blocksize / 4))

let transpose_lemma_i #w k i =
  let bs = w * 4 in
  let j = i / bs in
  let ki = (transpose_state k).[i / blocksize] in
  calc (==) {
    Seq.index (vec_v (Seq.index (transpose k) j)) (i % bs / 4);
    (==) { Math.Lemmas.modulo_division_lemma i 4 w }
    Seq.index (vec_v (Seq.index (transpose k) j)) (i / 4 % w);
    (==) { Math.Lemmas.division_multiplication_lemma i 4 w }
    Seq.index (vec_v (Seq.index (transpose k) (i / 4 / w))) (i / 4 % w);
    (==) { Lemmas.transpose_lemma_index #w k (i / 4); Math.Lemmas.division_multiplication_lemma i 4 16 }
    Seq.index ki (i / 4 % 16);
    (==) { Math.Lemmas.modulo_division_lemma i 4 16 }
    Seq.index ki (i % blocksize / 4);
    }


val xor_block_lemma_i: #w:lanes -> k:state w -> b:blocks w -> i:nat{i < w * blocksize} -> Lemma
  (let k_i = (transpose_state k).[i / blocksize] in
   let b_i = sub b (i / blocksize * blocksize) blocksize in
   (xor_block (transpose k) b).[i] == (Scalar.xor_block k_i b_i).[i % blocksize])

let xor_block_lemma_i #w k b i =
  let bs = w * 4 in
  let j = i / bs in
  let ki = (transpose_state k).[i / blocksize] in

  let b_i = sub b (i / blocksize * blocksize) blocksize in
  let block = sub b (i / 4 * 4) 4 in

  calc (==) {
    Seq.index (xor_block (transpose k) b) i;
    (==) { xor_block_vec_lemma_i #w (transpose k) b i }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le block) ^. (Seq.index (vec_v (transpose k).[j]) (i % bs / 4)))) (i % 4);
    (==) { transpose_lemma_i #w k i }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le block) ^. (Seq.index ki (i % blocksize / 4)))) (i % 4);
    };

  calc (==) {
    Seq.index (Scalar.xor_block ki b_i) (i % blocksize);
    (==) { xor_block_scalar_lemma_i ki b_i (i % blocksize); Math.Lemmas.modulo_modulo_lemma i 4 16 }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le #U32 #SEC (sub b_i (i % blocksize / 4 * 4) 4)) ^. ki.[i % blocksize / 4])) (i % 4);
    (==) { lemma_i_div_blocksize w i; Seq.Properties.slice_slice b (i / blocksize * blocksize)
            (i / blocksize * blocksize + blocksize) (i % blocksize / 4 * 4) (i % blocksize / 4 * 4 + 4) }
    Seq.index (uint_to_bytes_le ((uint_from_bytes_le #U32 #SEC block) ^. (Seq.index ki (i % blocksize / 4)))) (i % 4);
    }

///
///  map_blocks_vec
///

#set-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"

val encrypt_block_scalar_lemma_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter
  -> c:counter{w * c <= max_size_t /\ c0 + w <= max_size_t}
  -> b_i:Scalar.block
  -> i:nat{i < w} ->
  Lemma
  (let st_v0 = chacha20_init #w k n c0 in
   let st0 = Scalar.chacha20_init k n c0 in
   Scalar.chacha20_encrypt_block st0 (w * c + i) b_i `Seq.equal`
   Scalar.chacha20_encrypt_block (transpose_state st_v0).[i] (w * c) b_i)

let encrypt_block_scalar_lemma_i #w k n c0 c b i =
  let st_v0 = chacha20_init #w k n c0 in
  let st0 = Scalar.chacha20_init k n c0 in
  chacha20_init_lemma_i #w k n c0 i;
  assert ((transpose_state st_v0).[i] == Scalar.chacha20_init k n (c0 + i));
  kb_equiv_lemma #w k n c0 c i


val encrypt_block_lemma_st0_i:
    #w:lanes
  -> st_v0:state w
  -> c:counter{w * c <= max_size_t}
  -> b_v:blocks w
  -> j:nat{j < w * blocksize} ->
  Lemma
  (Math.Lemmas.cancel_mul_div w blocksize;
   let b = SeqLemmas.get_block_s #uint8 #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (chacha20_encrypt_block st_v0 c b_v).[j] ==
   (Scalar.chacha20_encrypt_block (transpose_state st_v0).[j / blocksize] (w * c) b).[j % blocksize])

let encrypt_block_lemma_st0_i #w st_v0 c b_v j =
  let k = chacha20_core c st_v0 in
  chacha20_core_lemma_i #w c st_v0 (j / blocksize);
  xor_block_lemma_i #w k b_v j


val encrypt_block_lemma_bs_i:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> c:counter{w * c <= max_size_t}
  -> b_v:blocks w
  -> j:nat{j < w * blocksize} ->
  Lemma
  (let st_v0 = chacha20_init #w k n c0 in
   let st0 = Scalar.chacha20_init k n c0 in
   Math.Lemmas.cancel_mul_div w blocksize;
   let b = SeqLemmas.get_block_s #uint8 #(w * blocksize) blocksize b_v j in
   div_mul_lt blocksize j w;
   (chacha20_encrypt_block st_v0 c b_v).[j] ==
   (Scalar.chacha20_encrypt_block st0 (w * c + j / blocksize) b).[j % blocksize])

let encrypt_block_lemma_bs_i #w k n c0 c b_v j =
  let st_v0 = chacha20_init #w k n c0 in
  let st0 = Scalar.chacha20_init k n c0 in
  Math.Lemmas.cancel_mul_div w blocksize;
  let b = SeqLemmas.get_block_s #uint8 #(w * blocksize) blocksize b_v j in
  encrypt_block_lemma_st0_i #w st_v0 c b_v j;
  div_mul_lt blocksize j w;
  encrypt_block_scalar_lemma_i #w k n c0 c b (j / blocksize)


val chacha20_map_blocks_multi_vec_equiv_pre_k:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:nat // n == hi_fv == len / (w * blocksize)
  -> hi_f:size_nat{w * hi_fv <= hi_f}
  -> i:nat{i < hi_fv}
  -> b_v:lseq uint8 (w * blocksize)
  -> j:nat{j < w * blocksize} ->
  Lemma
   (let st_v0 = chacha20_init #w k n c0 in
    let st0 = Scalar.chacha20_init k n c0 in
    let f_v = chacha20_encrypt_block st_v0 in
    let f = Scalar.chacha20_encrypt_block st0 in
    VecLemmas.map_blocks_multi_vec_equiv_pre_k w blocksize hi_fv hi_f f f_v i b_v j)

let chacha20_map_blocks_multi_vec_equiv_pre_k #w k n c0 hi_fv hi_f i b_v j =
  encrypt_block_lemma_bs_i #w k n c0 i b_v j


val update_sub_is_append:
    #a:Type0
  -> zero:a
  -> blocksize:size_pos
  -> len:nat{len < blocksize}
  -> b_v:lseq a len ->
  Lemma
   (let plain = create blocksize zero in
    let plain = update_sub plain 0 len b_v in
    let zeros = create (blocksize - len) zero in
    plain == concat b_v zeros)

let update_sub_is_append #a zero blocksize len b_v = admit()


val update_sub_get_block_lemma:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{j < len / blocksize * blocksize} -> Lemma
  (let blocksize_v = w * blocksize in
   let plain_v = create blocksize_v zero in
   let plain_v = update_sub plain_v 0 len b_v in
   div_mul_lt blocksize j w;
   Math.Lemmas.cancel_mul_div w blocksize;
   SeqLemmas.get_block_s #a #blocksize_v blocksize plain_v j ==
   SeqLemmas.get_block_s #a #len blocksize b_v j)

let update_sub_get_block_lemma #a w blocksize zero len b_v j = admit()


val update_sub_get_last_lemma:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> zero:a
  -> len:nat{len < w * blocksize}
  -> b_v:lseq a len
  -> j:nat{len / blocksize * blocksize <= j /\ j < len} -> Lemma
  (let blocksize_v = w * blocksize in
   let plain_v = create blocksize_v zero in
   let plain_v = update_sub plain_v 0 len b_v in
   div_mul_lt blocksize j w;
   Math.Lemmas.cancel_mul_div w blocksize;

   let block_l = SeqLemmas.get_last_s #a #len blocksize b_v in
   let plain = create blocksize zero in
   let plain = update_sub plain 0 (len % blocksize) block_l in

   SeqLemmas.get_block_s #a #blocksize_v blocksize plain_v j == plain)

let update_sub_get_last_lemma #a w blocksize zero len b_v j = admit()


val chacha20_map_blocks_vec_equiv_pre_k0:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{j < rem / blocksize * blocksize} ->
  Lemma
   (let st_v0 = chacha20_init #w k n c0 in
    let st0 = Scalar.chacha20_init k n c0 in
    let g_v = chacha20_encrypt_last st_v0 in
    let f = Scalar.chacha20_encrypt_block st0 in
    let g = Scalar.chacha20_encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

let chacha20_map_blocks_vec_equiv_pre_k0 #w k n c0 hi_fv rem b_v j =
  let blocksize_v = w * blocksize in
  let plain_v = create blocksize_v (u8 0) in
  let plain_v = update_sub plain_v 0 rem b_v in

  encrypt_block_lemma_bs_i #w k n c0 hi_fv plain_v j;
  update_sub_get_block_lemma w blocksize (u8 0) rem b_v j


val chacha20_map_blocks_vec_equiv_pre_k1:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{rem / blocksize * blocksize <= j /\ j < rem} ->
  Lemma
   (let st_v0 = chacha20_init #w k n c0 in
    let st0 = Scalar.chacha20_init k n c0 in
    let g_v = chacha20_encrypt_last st_v0 in
    let f = Scalar.chacha20_encrypt_block st0 in
    let g = Scalar.chacha20_encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

let chacha20_map_blocks_vec_equiv_pre_k1 #w k n c0 hi_fv rem b_v j =
  let blocksize_v = w * blocksize in
  // let st_v0 = chacha20_init #w k n c0 in
  // let st0 = Scalar.chacha20_init k n c0 in
  // let f_v = chacha20_encrypt_block st_v0 in
  // let g_v = chacha20_encrypt_last st_v0 in
  // let f = Scalar.chacha20_encrypt_block st0 in
  // let g = Scalar.chacha20_encrypt_last st0 in
  let plain_v = create blocksize_v (u8 0) in
  let plain_v = update_sub plain_v 0 rem b_v in
  assume (j / blocksize < w);
  assume (j / blocksize == rem / blocksize);
  assume (j % blocksize < rem % blocksize);
  encrypt_block_lemma_bs_i #w k n c0 hi_fv plain_v j;
  update_sub_get_last_lemma w blocksize (u8 0) rem b_v j


val chacha20_map_blocks_vec_equiv_pre_k:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> hi_fv:size_nat{w * hi_fv + w <= max_size_t} // n == hi_fv == len / (w * blocksize)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq uint8 rem
  -> j:nat{j < rem} ->
  Lemma
   (let st_v0 = chacha20_init #w k n c0 in
    let st0 = Scalar.chacha20_init k n c0 in
    let g_v = chacha20_encrypt_last st_v0 in
    let f = Scalar.chacha20_encrypt_block st0 in
    let g = Scalar.chacha20_encrypt_last st0 in
    VecLemmas.map_blocks_vec_equiv_pre_k w blocksize hi_fv f g g_v rem b_v j)

let chacha20_map_blocks_vec_equiv_pre_k #w k n c0 hi_fv rem b_v j =
  if j < rem / blocksize * blocksize then
    chacha20_map_blocks_vec_equiv_pre_k0 #w k n c0 hi_fv rem b_v j
  else
    chacha20_map_blocks_vec_equiv_pre_k1 #w k n c0 hi_fv rem b_v j


val lemma_chacha20_vec_equiv:
    #w:lanes
  -> k:key
  -> n:nonce
  -> c0:counter{c0 + w <= max_size_t}
  -> msg:seq uint8{length msg <= max_size_t} ->
  Lemma (chacha20_encrypt_bytes #w k n c0 msg `Seq.equal` Scalar.chacha20_encrypt_bytes k n c0 msg)

let lemma_chacha20_vec_equiv #w k n c0 msg =
  let blocksize_v = w * blocksize in

  let res = Scalar.chacha20_encrypt_bytes k n c0 msg in
  let res_v = chacha20_encrypt_bytes #w k n c0 msg in

  let st_v0 = chacha20_init #w k n c0 in
  let st0 = Scalar.chacha20_init k n c0 in

  let f_v = chacha20_encrypt_block st_v0 in
  let g_v = chacha20_encrypt_last st_v0 in

  let f = Scalar.chacha20_encrypt_block st0 in
  let g = Scalar.chacha20_encrypt_last st0 in
  assert (res_v == map_blocks blocksize_v msg f_v g_v);
  assert (res == map_blocks blocksize msg f g);

  let hi_fv = length msg / blocksize_v in
  let hi_f = w * hi_fv in
  Classical.forall_intro_3 (chacha20_map_blocks_multi_vec_equiv_pre_k #w k n c0 hi_fv hi_f);
  Classical.forall_intro_3 (chacha20_map_blocks_vec_equiv_pre_k #w k n c0 hi_fv);
  VecLemmas.lemma_map_blocks_vec w blocksize msg hi_fv f g f_v g_v
