module Hacl.Spec.Chacha20.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector

module Scalar = Spec.Chacha20
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
  [SMTPat (transpose_state (chacha20_core ctr s0))]
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

(* Up to this point is verified *)

val chacha20_init_lemma: #w:lanes -> k:key -> n:nonce -> ctr0:counter{ctr0+3 <= max_size_t} ->
    Lemma (transpose_state (chacha20_init #w k n ctr0) ==
	   map (Scalar.chacha20_init k n) (create4 ctr0 (ctr0+1) (ctr0+2) (ctr0+3)))
let chacha20_init_lemma #w k n ctro = ()

val xor_block_lemma: #w:lanes -> k:state w -> b:blocks w ->
    Lemma (ensures (
		let res = xor_block k b in
		res == map_blocks_multi size_block w b
		  (fun i -> Scalar.xor_block (transpose_state k).[i])))
	   [SMTPat (xor_block k b)]
let xor_block_lemma #w k b = admit()

#set-options "--z3rlimit 50"
val chacha20_encrypt_block_lemma: #w:lanes -> st0:state w -> incr:counter{w * incr <= max_size_t} -> b:blocks w ->
	Lemma (ensures (
		let res = chacha20_encrypt_block st0 incr b in
		let spec = map_blocks_multi size_block w b
		       (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr)) in
		res == spec))

#set-options "--z3rlimit 200 --max_ifuel 2"
let chacha20_encrypt_block_lemma #w st0 incr b =
  assert (chacha20_encrypt_block #w st0 incr b ==
	  xor_block (chacha20_core incr st0) b);
  match w with
  | 1 -> assert (length b == 64);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))
  | 4 -> assert (length b == 256);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b
		      (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))
  | 8 -> assert (length b == 512);
        assert (equal (chacha20_encrypt_block st0 incr b)
		      (map_blocks_multi size_block w b
		      (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))))

val chacha20_encrypt_last_lemma: #w:lanes -> st0:state w -> incr:counter{w * incr <= max_size_t} -> (len:size_nat{len < w * size_block}) -> b:lbytes len ->
	Lemma (ensures (
		let res = chacha20_encrypt_last st0 incr len b in
		res == map_blocks size_block b
		  (fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w*incr))
		  (fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w*incr))))

let chacha20_encrypt_last_lemma #w st0 incr len b =
  assert (chacha20_encrypt_last #w st0 incr len b ==
	  Seq.slice (chacha20_encrypt_block st0 incr
		    (update_sub (create (w * size_block) (u8 0)) 0 len b)) 0 len);
  let blocks = len / size_block in
  let rem = len % size_block in
  match w with
  | 1 -> assert (len < 64);
        assert (forall (i:nat). i < size_block * blocks ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (map_blocks size_block b
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);
        assert (forall (i:nat). (i >= size_block * blocks /\ i < len) ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (Scalar.chacha20_encrypt_last (transpose_state st0).[blocks] (w * incr) rem
							  (Seq.slice b (blocks * size_block) len)) (i % size_block));
	admit();
        assert (forall (i:nat). (i >= size_block * blocks /\ i < len) ==>
		  Seq.index (chacha20_encrypt_last st0 incr len b) i ==
		  Seq.index (map_blocks size_block b
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);

	admit()
  | _ -> admit()


(*
        assert (forall (i:nat). i / size_block < blocks ==>
		      Seq.index (chacha20_encrypt_last st0 incr len b) i ==`
		      Seq.index (map_blocks size_block b
			(fun i -> Scalar.chacha20_encrypt_block (transpose_state st0).[i] (w * incr))
			(fun i -> Scalar.chacha20_encrypt_last (transpose_state st0).[i] (w * incr))) i);
	admit()
*)


let chacha20_update_lemma (st0: Scalar.state) (msg: bytes{length msg / size_block + v st0.[12] <= max_size_t}) =
  let len = length msg in
  let blocks = len / (4*size_block) in
  let rem = len % (4*size_block) in


  admit();
  assert (Scalar.chacha20_update st0 msg ==
	  map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0));
  assert (forall (i:nat). i < 4 * size_block * blocks ==>
	 Seq.index
	  (map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0)) i ==
	 Seq.index (Scalar.chacha20_encrypt_block st0 (i/size_block) (Seq.slice msg (i*size_block) ((i+1)*size_block))) (i % size_block));
  assert (Seq.equal
	  (map_blocks size_block msg
	    (Scalar.chacha20_encrypt_block st0)
	    (Scalar.chacha20_encrypt_last st0))
	  (map_blocks (4*size_block) msg
	    (fun i b4 ->
	      map_blocks_multi size_block 4 b4
		(fun j b -> Scalar.chacha20_encrypt_block (Scalar.add_counter j st0) (4*i) b))
            (fun i l b4 ->
	      map_blocks size_block b4
		(fun j b -> Scalar.chacha20_encrypt_block (Scalar.add_counter j st0) (4*i) b)
		(fun j l b -> Scalar.chacha20_encrypt_last (Scalar.add_counter j st0) (4*i) l b))))


val chacha20_encrypt_bytes_lemma: #w:lanes ->
    k:key -> n:nonce -> c:counter ->
    msg:bytes{length msg/size_block + c <= max_size_t} ->
    Lemma (chacha20_encrypt_bytes #w k n c msg ==
    Scalar.chacha20_encrypt_bytes k n c msg)
