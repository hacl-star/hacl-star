module Hacl.Spec.Chacha20.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector

module Scalar = Spec.Chacha20
module Loops = Lib.LoopCombinators

open Hacl.Spec.Chacha20.Vec

#reset-options "--z3rlimit 50 --max_fuel 1"

val line_lemma_i:
  #w:lanes
  -> a:idx -> b:idx -> d:idx
  -> s:rotval U32 -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (line #w a b d s m)).[i] ==
	 Scalar.line a b d s (transpose_state #w m).[i])
let line_lemma_i #w a b d s m i =
  eq_intro (transpose_state (line #w a b d s m)).[i] (Scalar.line a b d s (transpose_state #w m).[i])

val line_lemma: #w:lanes
  -> a:idx -> b:idx -> d:idx
  -> s:rotval U32 -> m:state w ->
  Lemma (transpose_state (line #w a b d s m) ==
	 map (Scalar.line a b d s) (transpose_state #w m))
let line_lemma #w a b d s m =
  let lp = transpose_state (line #w a b d s m) in
  let rp = map (Scalar.line a b d s) (transpose_state #w m) in
  match w with
  | 1 ->
    line_lemma_i #w a b d s m 0;
    eq_intro lp rp
  | 4 ->
    line_lemma_i #w a b d s m 0;
    line_lemma_i #w a b d s m 1;
    line_lemma_i #w a b d s m 2;
    line_lemma_i #w a b d s m 3;
    eq_intro lp rp
  | 8 ->
    line_lemma_i #w a b d s m 0;
    line_lemma_i #w a b d s m 1;
    line_lemma_i #w a b d s m 2;
    line_lemma_i #w a b d s m 3;
    line_lemma_i #w a b d s m 4;
    line_lemma_i #w a b d s m 5;
    line_lemma_i #w a b d s m 6;
    line_lemma_i #w a b d s m 7;
    eq_intro lp rp

val quarter_round_map_lemma_i:
  #w:lanes
  -> a:idx -> b:idx -> c:idx -> d:idx
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (quarter_round #w a b c d m)).[i] == Scalar.quarter_round a b c d (transpose_state m).[i])
let quarter_round_map_lemma_i #w a b c d m i =
  let lp0 = line a b d (size 16) m in
  let lp1 = line c d b (size 12) lp0 in
  let lp2 = line a b d (size 8) lp1 in
  let lp3 = line c d b (size 7) lp2 in
  assert (quarter_round #w a b c d m == lp3);
  line_lemma a b d (size 16) m;
  line_lemma c d b (size 12) lp0;
  line_lemma a b d (size 8) lp1;
  line_lemma c d b (size 7) lp2;
  eq_intro (transpose_state (quarter_round #w a b c d m)).[i] (Scalar.quarter_round a b c d (transpose_state m).[i])

val quarter_round_map_lemma: #w:lanes
  -> a:idx -> b:idx -> c:idx -> d:idx
  -> m:state w ->
  Lemma (transpose_state (quarter_round #w a b c d m) == map (Scalar.quarter_round a b c d) (transpose_state m))
  //[SMTPat (transpose_state (quarter_round #w a b c d m))]
let quarter_round_map_lemma #w a b c d m =
  let lp = transpose_state (quarter_round #w a b c d m) in
  let rp = map (Scalar.quarter_round a b c d) (transpose_state m) in
  match w with
  | 1 ->
    quarter_round_map_lemma_i #w a b c d m 0;
    eq_intro lp rp
  | 4 ->
    quarter_round_map_lemma_i #w a b c d m 0;
    quarter_round_map_lemma_i #w a b c d m 1;
    quarter_round_map_lemma_i #w a b c d m 2;
    quarter_round_map_lemma_i #w a b c d m 3;
    eq_intro lp rp
  | 8 ->
    quarter_round_map_lemma_i #w a b c d m 0;
    quarter_round_map_lemma_i #w a b c d m 1;
    quarter_round_map_lemma_i #w a b c d m 2;
    quarter_round_map_lemma_i #w a b c d m 3;
    quarter_round_map_lemma_i #w a b c d m 4;
    quarter_round_map_lemma_i #w a b c d m 5;
    quarter_round_map_lemma_i #w a b c d m 6;
    quarter_round_map_lemma_i #w a b c d m 7;
    eq_intro lp rp

val column_round_map_lemma_i: #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (column_round #w m)).[i] == Scalar.column_round (transpose_state m).[i])
let column_round_map_lemma_i #w m i =
  let lp0 = quarter_round 0 4 8  12 m in
  let lp1 = quarter_round 1 5 9  13 lp0 in
  let lp2 = quarter_round 2 6 10 14 lp1 in
  let lp3 = quarter_round 3 7 11 15 lp2 in
  assert (column_round #w m == lp3);
  quarter_round_map_lemma 0 4 8  12 m;
  quarter_round_map_lemma 1 5 9  13 lp0;
  quarter_round_map_lemma 2 6 10 14 lp1;
  quarter_round_map_lemma 3 7 11 15 lp2;
  eq_intro (transpose_state (column_round #w m)).[i] (Scalar.column_round (transpose_state m).[i])

val column_round_map_lemma: #w:lanes
  -> m:state w ->
  Lemma (transpose_state (column_round #w m) == map (Scalar.column_round) (transpose_state m))
  [SMTPat (transpose_state (column_round #w m))]
let column_round_map_lemma #w m =
  let lp = transpose_state (column_round #w m) in
  let rp = map (Scalar.column_round) (transpose_state m) in
  match w with
  | 1 ->
    column_round_map_lemma_i #w m 0;
    eq_intro lp rp
  | 4 ->
    column_round_map_lemma_i #w m 0;
    column_round_map_lemma_i #w m 1;
    column_round_map_lemma_i #w m 2;
    column_round_map_lemma_i #w m 3;
    eq_intro lp rp
  | 8 ->
    column_round_map_lemma_i #w m 0;
    column_round_map_lemma_i #w m 1;
    column_round_map_lemma_i #w m 2;
    column_round_map_lemma_i #w m 3;
    column_round_map_lemma_i #w m 4;
    column_round_map_lemma_i #w m 5;
    column_round_map_lemma_i #w m 6;
    column_round_map_lemma_i #w m 7;
    eq_intro lp rp

val diagonal_round_map_lemma_i: #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (diagonal_round #w m)).[i] == Scalar.diagonal_round (transpose_state m).[i])
let diagonal_round_map_lemma_i #w m i =
  let lp0 = quarter_round 0 5 10 15 m in
  let lp1 = quarter_round 1 6 11 12 lp0 in
  let lp2 = quarter_round 2 7 8  13 lp1 in
  let lp3 = quarter_round 3 4 9  14 lp2 in
  assert (diagonal_round #w m == lp3);
  quarter_round_map_lemma 0 5 10 15 m;
  quarter_round_map_lemma 1 6 11 12 lp0;
  quarter_round_map_lemma 2 7 8  13 lp1;
  quarter_round_map_lemma 3 4 9  14 lp2;
  eq_intro (transpose_state (diagonal_round #w m)).[i] (Scalar.diagonal_round (transpose_state m).[i])

val diagonal_round_map_lemma: #w:lanes
  -> m:state w ->
  Lemma (transpose_state (diagonal_round #w m) == map (Scalar.diagonal_round) (transpose_state m))
  [SMTPat (transpose_state (diagonal_round #w m))]
let diagonal_round_map_lemma #w m =
  let lp = transpose_state (diagonal_round #w m) in
  let rp = map (Scalar.diagonal_round) (transpose_state m) in
  match w with
  | 1 ->
    diagonal_round_map_lemma_i #w m 0;
    eq_intro lp rp
  | 4 ->
    diagonal_round_map_lemma_i #w m 0;
    diagonal_round_map_lemma_i #w m 1;
    diagonal_round_map_lemma_i #w m 2;
    diagonal_round_map_lemma_i #w m 3;
    eq_intro lp rp
  | 8 ->
    diagonal_round_map_lemma_i #w m 0;
    diagonal_round_map_lemma_i #w m 1;
    diagonal_round_map_lemma_i #w m 2;
    diagonal_round_map_lemma_i #w m 3;
    diagonal_round_map_lemma_i #w m 4;
    diagonal_round_map_lemma_i #w m 5;
    diagonal_round_map_lemma_i #w m 6;
    diagonal_round_map_lemma_i #w m 7;
    eq_intro lp rp

val double_round_map_lemma_i:
    #w:lanes
  -> m:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (double_round #w m)).[i] == Scalar.double_round (transpose_state m).[i])
let double_round_map_lemma_i #w m i = ()


val double_round_map_lemma: #w:lanes
  -> m:state w ->
  Lemma (transpose_state (double_round #w m) == map (Scalar.double_round) (transpose_state m))
  [SMTPat (transpose_state (double_round #w m))]
let double_round_map_lemma #w m =
  let lp = transpose_state (double_round #w m) in
  let rp = map (Scalar.double_round) (transpose_state m) in
  match w with
  | 1 ->
    double_round_map_lemma_i #w m 0;
    eq_intro lp rp
  | 4 ->
    double_round_map_lemma_i #w m 0;
    double_round_map_lemma_i #w m 1;
    double_round_map_lemma_i #w m 2;
    double_round_map_lemma_i #w m 3;
    eq_intro lp rp
  | 8 ->
    double_round_map_lemma_i #w m 0;
    double_round_map_lemma_i #w m 1;
    double_round_map_lemma_i #w m 2;
    double_round_map_lemma_i #w m 3;
    double_round_map_lemma_i #w m 4;
    double_round_map_lemma_i #w m 5;
    double_round_map_lemma_i #w m 6;
    double_round_map_lemma_i #w m 7;
    eq_intro lp rp

let scalar_rounds (m:Scalar.state) : Scalar.state =
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round (
  Scalar.double_round (Scalar.double_round m)))))))))

val scalar_rounds_unroll_lemma: m:Scalar.state ->
  Lemma (scalar_rounds m == Scalar.rounds m)
  [SMTPat (Scalar.rounds m)]
let scalar_rounds_unroll_lemma m =
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
  unfold_repeat 10 Scalar.double_round m 9;
  ()

val rounds_lemma_i: #w:lanes
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
  double_round_map_lemma #w m;
  assert ((transpose_state m1).[i] == Scalar.double_round ms);
  double_round_map_lemma #w m1;
  assert ((transpose_state m2).[i] == Scalar.double_round (Scalar.double_round ms));
  double_round_map_lemma #w m2;
  double_round_map_lemma #w m3;
  double_round_map_lemma #w m4;
  double_round_map_lemma #w m5;
  double_round_map_lemma #w m6;
  double_round_map_lemma #w m7;
  double_round_map_lemma #w m8;
  double_round_map_lemma #w m9;
  assert ((transpose_state m10).[i] == scalar_rounds ms);
  scalar_rounds_unroll_lemma ms

val rounds_lemma: #w:lanes
  -> m:state w ->
  Lemma (transpose_state (rounds #w m) == map Scalar.rounds (transpose_state m))
  [SMTPat (transpose_state (rounds #w m))]
let rounds_lemma #w m =
  let lp = transpose_state (rounds #w m) in
  let rp = map Scalar.rounds (transpose_state m) in
  match w with
  | 1 ->
    rounds_lemma_i #w m 0;
    eq_intro lp rp
  | 4 ->
    rounds_lemma_i #w m 0;
    rounds_lemma_i #w m 1;
    rounds_lemma_i #w m 2;
    rounds_lemma_i #w m 3;
    eq_intro lp rp
  | 8 ->
    rounds_lemma_i #w m 0;
    rounds_lemma_i #w m 1;
    rounds_lemma_i #w m 2;
    rounds_lemma_i #w m 3;
    rounds_lemma_i #w m 4;
    rounds_lemma_i #w m 5;
    rounds_lemma_i #w m 6;
    rounds_lemma_i #w m 7;
    eq_intro lp rp

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

val sum_state_lemma: #w:lanes
  -> st1:state w
  -> st2:state w ->
  Lemma (transpose_state (sum_state st1 st2) ==
	 map2 Scalar.sum_state (transpose_state st1) (transpose_state st2))
  [SMTPat (transpose_state (sum_state st1 st2))]
let sum_state_lemma #w st1 st2 =
  let lp = transpose_state (sum_state st1 st2) in
  let rp = map2 Scalar.sum_state (transpose_state st1) (transpose_state st2) in
  match w with
  | 1 ->
    sum_state_lemma_i #w st1 st2 0;
    eq_intro lp rp
  | 4 ->
    sum_state_lemma_i #w st1 st2 0;
    sum_state_lemma_i #w st1 st2 1;
    sum_state_lemma_i #w st1 st2 2;
    sum_state_lemma_i #w st1 st2 3;
    eq_intro lp rp
  | 8 ->
    sum_state_lemma_i #w st1 st2 0;
    sum_state_lemma_i #w st1 st2 1;
    sum_state_lemma_i #w st1 st2 2;
    sum_state_lemma_i #w st1 st2 3;
    sum_state_lemma_i #w st1 st2 4;
    sum_state_lemma_i #w st1 st2 5;
    sum_state_lemma_i #w st1 st2 6;
    sum_state_lemma_i #w st1 st2 7;
    eq_intro lp rp

val add_counter_lemma_i:
    #w:lanes
  -> st:state w
  -> ctr:counter{w * ctr <= max_size_t}
  -> i:nat{i < w} ->
  Lemma ((transpose_state (add_counter #w ctr st)).[i] ==
	 Scalar.add_counter (w * ctr) (transpose_state st).[i])
let add_counter_lemma_i #w st ctr i =
  FStar.Math.Lemmas.modulo_lemma (w * ctr) (pow2 32);
  uintv_extensionality (u32 w *! u32 ctr) (u32 (w * ctr));
  eq_intro (transpose_state (add_counter #w ctr st)).[i]
	   (Scalar.add_counter (w * ctr) (transpose_state st).[i])

val add_counter_lemma: #w:lanes
  -> st:state w
  -> ctr:counter{w * ctr <= max_size_t} ->
  Lemma (transpose_state (add_counter #w ctr st) ==
	 map (Scalar.add_counter (w * ctr)) (transpose_state st))
  [SMTPat (transpose_state (add_counter #w ctr st))]
let add_counter_lemma #w st ctr =
  let lp = transpose_state (add_counter #w ctr st) in
  let rp = map (Scalar.add_counter (w * ctr)) (transpose_state st) in
  match w with
  | 1 ->
    add_counter_lemma_i #w st ctr 0;
    eq_intro lp rp
  | 4 ->
    add_counter_lemma_i #w st ctr 0;
    add_counter_lemma_i #w st ctr 1;
    add_counter_lemma_i #w st ctr 2;
    add_counter_lemma_i #w st ctr 3;
    eq_intro lp rp
  | 8 ->
    add_counter_lemma_i #w st ctr 0;
    add_counter_lemma_i #w st ctr 1;
    add_counter_lemma_i #w st ctr 2;
    add_counter_lemma_i #w st ctr 3;
    add_counter_lemma_i #w st ctr 4;
    add_counter_lemma_i #w st ctr 5;
    add_counter_lemma_i #w st ctr 6;
    add_counter_lemma_i #w st ctr 7;
    eq_intro lp rp

val chacha20_core_lemma_i:
    #w:lanes
  -> ctr:counter{w * ctr <= max_size_t}
  -> s0:state w
  -> i:nat{i < w} ->
  Lemma ((transpose_state (chacha20_core ctr s0)).[i] ==
	 Scalar.chacha20_core (w * ctr) (transpose_state s0).[i])
let chacha20_core_lemma_i #w ctr s0 i = ()

val chacha20_core_lemma: #w:lanes
  -> ctr:counter{w * ctr <= max_size_t}
  -> s0:state w ->
  Lemma (transpose_state (chacha20_core ctr s0) ==
	map (Scalar.chacha20_core (w * ctr)) (transpose_state s0))
let chacha20_core_lemma #w ctr s0 =
  let lp = transpose_state (chacha20_core ctr s0) in
  let rp = map (Scalar.chacha20_core (w * ctr)) (transpose_state s0) in
  match w with
  | 1 ->
    chacha20_core_lemma_i #w ctr s0 0;
    eq_intro lp rp
  | 4 ->
    chacha20_core_lemma_i #w ctr s0 0;
    chacha20_core_lemma_i #w ctr s0 1;
    chacha20_core_lemma_i #w ctr s0 2;
    chacha20_core_lemma_i #w ctr s0 3;
    eq_intro lp rp
  | 8 ->
    chacha20_core_lemma_i #w ctr s0 0;
    chacha20_core_lemma_i #w ctr s0 1;
    chacha20_core_lemma_i #w ctr s0 2;
    chacha20_core_lemma_i #w ctr s0 3;
    chacha20_core_lemma_i #w ctr s0 4;
    chacha20_core_lemma_i #w ctr s0 5;
    chacha20_core_lemma_i #w ctr s0 6;
    chacha20_core_lemma_i #w ctr s0 7;
    eq_intro lp rp

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
  uintv_extensionality (vec_v c).[i] (u32 i);
  assert ((vec_v c).[i] == u32 i);

  let res = st.[12] <- st.[12] +| c in
  let res1 = st1.[12] <- st1.[12] +. u32 i in
  eq_intro (transpose_state res).[i] res1;
  assert ((transpose_state res).[i] == res1);
  assert (res1.[12] == u32 ctr0 +. u32 i);
  assert (v (u32 ctr0 +. u32 i) == v (u32 (ctr0 + i)));
  uintv_extensionality (u32 ctr0 +. u32 i) (u32 (ctr0 + i));
  assert (res1.[12] == u32 (ctr0 + i));

  let res2 = Scalar.chacha20_init k n (ctr0 + i) in
  chacha20_init_equiv_lemma k n ctr0;
  chacha20_init_equiv_lemma k n (ctr0 + i);
  eq_intro res1 res2

val load_blocks_lemma_index:
    #w:lanes
  -> b:blocks w
  -> i:nat{i < w * 16} ->
  Lemma (
    (vec_v (load_blocks #w b).[i / w]).[i % w] ==
    uint_from_bytes_le (sub b (4 * i) 4))
let load_blocks_lemma_index #w b i =
  let j = i / w in
  let res = load_blocks #w b in
  assert (res.[j] == load_blocks_inner #w b j);
  assert (res.[j] == vec_from_bytes_le U32 w (sub b (j * w * 4) (w * 4)));
  assert (vec_v res.[j] == uints_from_bytes_le (sub b (j * w * 4) (w * 4)));
  let j1 = i % w in
  let b_j = sub b (j * w * 4) (w * 4) in
  index_uints_from_bytes_le b_j j1;
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
    index (store_blocks #w st) i ==
    (uint_to_bytes_le (vec_v st.[j / w ]).[j % w]).[i % 4])
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
    index (Scalar.xor_block k b) i ==
    (uint_to_bytes_le ((uint_from_bytes_le (sub b (4 * j) 4)) ^. k.[j])).[i % 4])
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

val vec_interleave_low_uint32_4: a:uint32xN 4 -> b:uint32xN 4 ->
  Lemma
  (vec_v (vec_interleave_low a b) ==
   create4 (vec_v a).[0] (vec_v b).[0] (vec_v a).[1] (vec_v b).[1])
let vec_interleave_low_uint32_4 a b = admit()

val vec_interleave_low_uint32_4_2: a:uint32xN 4 -> b:uint32xN 4 ->
  Lemma
  (vec_v (cast U32 4 (vec_interleave_low (cast U64 2 a) (cast U64 2 b))) ==
   create4 (vec_v a).[0] (vec_v a).[1] (vec_v b).[0] (vec_v b).[1])
let vec_interleave_low_uint32_4_2 a b = admit()

val vec_interleave_low_uint32_8: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (vec_interleave_low a b) ==
   create8 (vec_v a).[0] (vec_v b).[0] (vec_v a).[1] (vec_v b).[1] (vec_v a).[4] (vec_v b).[4] (vec_v a).[5] (vec_v b).[5])
let vec_interleave_low_uint32_8 a b = admit()

val vec_interleave_low_uint32_8_4: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (cast U32 8 (vec_interleave_low (cast U64 4 a) (cast U64 4 b))) ==
   create8 (vec_v a).[0] (vec_v a).[1] (vec_v b).[0] (vec_v b).[1] (vec_v a).[4] (vec_v a).[5] (vec_v b).[4] (vec_v b).[5])
let vec_interleave_low_uint32_8_4 a b = admit()

val vec_interleave_low_uint32_8_2: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (cast U32 8 (vec_interleave_low (cast U128 2 a) (cast U128 2 b))) ==
   create8 (vec_v a).[0] (vec_v a).[1] (vec_v a).[2] (vec_v a).[3] (vec_v b).[0] (vec_v b).[1] (vec_v b).[2] (vec_v b).[3])
let vec_interleave_low_uint32_8_2 a b = admit()

val vec_interleave_high_uint32_4: a:uint32xN 4 -> b:uint32xN 4 ->
  Lemma
  (vec_v (vec_interleave_high a b) ==
   create4 (vec_v a).[2] (vec_v b).[2] (vec_v a).[3] (vec_v b).[3])
let vec_interleave_high_uint32_4 a b = admit()

val vec_interleave_high_uint32_4_2: a:uint32xN 4 -> b:uint32xN 4 ->
  Lemma
  (vec_v (cast U32 4 (vec_interleave_high (cast U64 2 a) (cast U64 2 b))) ==
   create4 (vec_v a).[2] (vec_v a).[3] (vec_v b).[2] (vec_v b).[3])
let vec_interleave_high_uint32_4_2 a b = admit()

val vec_interleave_high_uint32_8: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (vec_interleave_high a b) ==
   create8 (vec_v a).[2] (vec_v b).[2] (vec_v a).[3] (vec_v b).[3] (vec_v a).[6] (vec_v b).[6] (vec_v a).[7] (vec_v b).[7])
let vec_interleave_high_uint32_8 a b = admit()

val vec_interleave_high_uint32_8_4: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (cast U32 8 (vec_interleave_high (cast U64 4 a) (cast U64 4 b))) ==
   create8 (vec_v a).[2] (vec_v a).[3] (vec_v b).[2] (vec_v b).[3] (vec_v a).[6] (vec_v a).[7] (vec_v b).[6] (vec_v b).[7])
let vec_interleave_high_uint32_8_4 a b = admit()

val vec_interleave_high_uint32_8_2: a:uint32xN 8 -> b:uint32xN 8 ->
  Lemma
  (vec_v (cast U32 8 (vec_interleave_high (cast U128 2 a) (cast U128 2 b))) ==
   create8 (vec_v a).[4] (vec_v a).[5] (vec_v a).[6] (vec_v a).[7] (vec_v b).[4] (vec_v b).[5] (vec_v b).[6] (vec_v b).[7])
let vec_interleave_high_uint32_8_2 a b = admit()

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
  vec_interleave_low_uint32_4 v0 v1;
  let v1' = vec_interleave_high v0 v1 in
  vec_interleave_high_uint32_4 v0 v1;
  let v2' = vec_interleave_low v2 v3 in
  vec_interleave_low_uint32_4 v2 v3;
  let v3' = vec_interleave_high v2 v3 in
  vec_interleave_high_uint32_4 v2 v3;
  let v0'' = cast U32 4 (vec_interleave_low (cast U64 2 v0') (cast U64 2 v2')) in
  vec_interleave_low_uint32_4_2 v0' v2';
  let v1'' = cast U32 4 (vec_interleave_high (cast U64 2 v0') (cast U64 2 v2')) in
  vec_interleave_high_uint32_4_2 v0' v2';
  let v2'' = cast U32 4 (vec_interleave_low (cast U64 2 v1') (cast U64 2 v3')) in
  vec_interleave_low_uint32_4_2 v1' v3';
  let v3'' = cast U32 4 (vec_interleave_high (cast U64 2 v1') (cast U64 2 v3')) in
  vec_interleave_high_uint32_4_2 v1' v3';
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
  vec_interleave_low_uint32_8 v0 v1;
  let r0: lseq uint32 8 = create8 v0.(0) v1.(0) v0.(1) v1.(1) v0.(4) v1.(4) v0.(5) v1.(5) in
  assert (vec_v v0' == r0);
  let v1' = vec_interleave_high v0 v1 in
  vec_interleave_high_uint32_8 v0 v1;
  let r1: lseq uint32 8 = create8 v0.(2) v1.(2) v0.(3) v1.(3) v0.(6) v1.(6) v0.(7) v1.(7) in
  assert (vec_v v1' == r1);
  let v2' = vec_interleave_low v2 v3 in
  vec_interleave_low_uint32_8 v2 v3;
  let r2: lseq uint32 8 = create8 v2.(0) v3.(0) v2.(1) v3.(1) v2.(4) v3.(4) v2.(5) v3.(5) in
  assert (vec_v v2' == r2);
  let v3' = vec_interleave_high v2 v3 in
  vec_interleave_high_uint32_8 v2 v3;
  let r3: lseq uint32 8 = create8 v2.(2) v3.(2) v2.(3) v3.(3) v2.(6) v3.(6) v2.(7) v3.(7) in
  assert (vec_v v3' == r3);
  let v4' = vec_interleave_low v4 v5 in
  vec_interleave_low_uint32_8 v4 v5;
  let r4: lseq uint32 8 = create8 v4.(0) v5.(0) v4.(1) v5.(1) v4.(4) v5.(4) v4.(5) v5.(5) in
  assert (vec_v v4' == r4);
  let v5' = vec_interleave_high v4 v5 in
  vec_interleave_high_uint32_8 v4 v5;
  let r5: lseq uint32 8 = create8 v4.(2) v5.(2) v4.(3) v5.(3) v4.(6) v5.(6) v4.(7) v5.(7) in
  assert (vec_v v5' == r5);
  let v6' = vec_interleave_low v6 v7 in
  vec_interleave_low_uint32_8 v6 v7;
  let r6: lseq uint32 8 = create8 v6.(0) v7.(0) v6.(1) v7.(1) v6.(4) v7.(4) v6.(5) v7.(5) in
  assert (vec_v v6' == r6);
  let v7' = vec_interleave_high v6 v7 in
  vec_interleave_high_uint32_8 v6 v7;
  let r7: lseq uint32 8 = create8 v6.(2) v7.(2) v6.(3) v7.(3) v6.(6) v7.(6) v6.(7) v7.(7) in
  assert (vec_v v7' == r7);

  let v0'' = cast U32 8 (vec_interleave_low (cast U64 4 v0') (cast U64 4 v2')) in
  vec_interleave_low_uint32_8_4 v0' v2';
  let r0': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v0.(4) v1.(4) v2.(4) v3.(4) in
  assert (vec_v v0'' == r0');

  let v1'' = cast U32 8 (vec_interleave_high (cast U64 4 v0') (cast U64 4 v2')) in
  vec_interleave_high_uint32_8_4 v0' v2';
  let r1': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v0.(5) v1.(5) v2.(5) v3.(5) in
  assert (vec_v v1'' == r1');

  let v2'' = cast U32 8 (vec_interleave_low (cast U64 4 v1') (cast U64 4 v3')) in
  vec_interleave_low_uint32_8_4 v1' v3';
  let r2': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v0.(6) v1.(6) v2.(6) v3.(6) in
  assert (vec_v v2'' == r2');

  let v3'' = cast U32 8 (vec_interleave_high (cast U64 4 v1') (cast U64 4 v3')) in
  vec_interleave_high_uint32_8_4 v1' v3';
  let r3': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v0.(7) v1.(7) v2.(7) v3.(7) in
  assert (vec_v v3'' == r3');

  let v4'' = cast U32 8 (vec_interleave_low (cast U64 4 v4') (cast U64 4 v6')) in
  vec_interleave_low_uint32_8_4 v4' v6';
  let r4': lseq uint32 8 = create8 v4.(0) v5.(0) v6.(0) v7.(0) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v4'' == r4');

  let v5'' = cast U32 8 (vec_interleave_high (cast U64 4 v4') (cast U64 4 v6')) in
  vec_interleave_high_uint32_8_4 v4' v6';
  let r5': lseq uint32 8 = create8 v4.(1) v5.(1) v6.(1) v7.(1) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v5'' == r5');

  let v6'' = cast U32 8 (vec_interleave_low (cast U64 4 v5') (cast U64 4 v7')) in
  vec_interleave_low_uint32_8_4 v5' v7';
  let r6': lseq uint32 8 = create8 v4.(2) v5.(2) v6.(2) v7.(2) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v6'' == r6');

  let v7'' = cast U32 8 (vec_interleave_high (cast U64 4 v5') (cast U64 4 v7')) in
  vec_interleave_high_uint32_8_4 v5' v7';
  let r7': lseq uint32 8 = create8 v4.(3) v5.(3) v6.(3) v7.(3) v4.(7) v5.(7) v6.(7) v7.(7) in
  assert (vec_v v7'' == r7');

  let v0''' = cast U32 8 (vec_interleave_low (cast U128 2 v0'') (cast U128 2 v4'')) in
  vec_interleave_low_uint32_8_2 v0'' v4'';
  let r0'': lseq uint32 8 = create8 v0.(0) v1.(0) v2.(0) v3.(0) v4.(0) v5.(0) v6.(0) v7.(0) in
  assert (vec_v v0''' == r0'');

  let v1''' = cast U32 8 (vec_interleave_high (cast U128 2 v0'') (cast U128 2 v4'')) in
  vec_interleave_high_uint32_8_2 v0'' v4'';
  let r1'': lseq uint32 8 = create8 v0.(4) v1.(4) v2.(4) v3.(4) v4.(4) v5.(4) v6.(4) v7.(4) in
  assert (vec_v v1''' == r1'');

  let v2''' = cast U32 8 (vec_interleave_low (cast U128 2 v1'') (cast U128 2 v5'')) in
  vec_interleave_low_uint32_8_2 v1'' v5'';
  let r2'': lseq uint32 8 = create8 v0.(1) v1.(1) v2.(1) v3.(1) v4.(1) v5.(1) v6.(1) v7.(1) in
  assert (vec_v v2''' == r2'');

  let v3''' = cast U32 8 (vec_interleave_high (cast U128 2 v1'') (cast U128 2 v5'')) in
  vec_interleave_high_uint32_8_2 v1'' v5'';
  let r3'': lseq uint32 8 = create8 v0.(5) v1.(5) v2.(5) v3.(5) v4.(5) v5.(5) v6.(5) v7.(5) in
  assert (vec_v v3''' == r3'');

  let v4''' = cast U32 8 (vec_interleave_low (cast U128 2 v2'') (cast U128 2 v6'')) in
  vec_interleave_low_uint32_8_2 v2'' v6'';
  let r4'': lseq uint32 8 = create8 v0.(2) v1.(2) v2.(2) v3.(2) v4.(2) v5.(2) v6.(2) v7.(2) in
  assert (vec_v v4''' == r4'');

  let v5''' = cast U32 8 (vec_interleave_high (cast U128 2 v2'') (cast U128 2 v6'')) in
  vec_interleave_high_uint32_8_2 v2'' v6'';
  let r5'': lseq uint32 8 = create8 v0.(6) v1.(6) v2.(6) v3.(6) v4.(6) v5.(6) v6.(6) v7.(6) in
  assert (vec_v v5''' == r5'');

  let v6''' = cast U32 8 (vec_interleave_low (cast U128 2 v3'') (cast U128 2 v7'')) in
  vec_interleave_low_uint32_8_2 v3'' v7'';
  let r6'': lseq uint32 8 = create8 v0.(3) v1.(3) v2.(3) v3.(3) v4.(3) v5.(3) v6.(3) v7.(3) in
  assert (vec_v v6''' == r6'');

  let v7''' = cast U32 8 (vec_interleave_high (cast U128 2 v3'') (cast U128 2 v7'')) in
  vec_interleave_high_uint32_8_2 v3'' v7'';
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
    index (xor_block k b) i ==
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

#set-options "--max_fuel 0"

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
  chacha20_core_lemma #w incr st0;
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

#reset-options "--z3rlimit 150 --max_fuel 0"

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
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v b + ctr0 + i) (w * incr) (modulus U32);
  uintv_extensionality lp rp

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
  let k1 = Scalar.add_counter (w * incr + i) st1 in
  assert (k1.[12] == u32 ctr0 +. u32 (w * incr + i));
  let k2 = Scalar.add_counter (w * incr) st2 in
  assert (k2.[12] == u32 (ctr0 + i) +. u32 (w * incr));
  uintv_extensionality k1.[12] k2.[12];
  eq_intro k1 k2;
  let k = Scalar.rounds k1 in
  let k1 = Scalar.sum_state k st1 in
  assert (k1.[12] == k.[12] +. u32 ctr0);
  let k2 = Scalar.sum_state k st2 in
  assert (k2.[12] == k.[12] +. u32 (ctr0 + i));
  assert (forall (j:nat). j < 16 /\ j <> 12 ==> k1.[j] == k2.[j]);
  let k1 = Scalar.add_counter (w * incr + i) k1 in
  assert (k1.[12] == k.[12] +. u32 ctr0 +. u32 (w * incr + i));
  let k2 = Scalar.add_counter (w * incr) k2 in
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
