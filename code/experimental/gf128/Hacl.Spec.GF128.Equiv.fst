module Hacl.Spec.GF128.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

open Spec.GaloisField

module Loops = Lib.LoopCombinators
module PLoops = Lib.Loops.Lemmas
module S = Spec.GF128

include Hacl.Spec.GF128.Vec

#set-options "--z3rlimit 50 --max_fuel 1"

val gf128_ni_repeati_extensionality:
    n:nat
  -> r:elem
  -> f:(i:nat{i < n * 4} -> elem -> elem)
  -> f_vec:(i:nat{i < n} -> elem -> elem)
  -> acc0:elem ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:elem). f_vec i acc == f (4*i+3) (f (4*i+2) (f (4*i+1) (f (4*i) acc)))))
  (ensures  Loops.repeati n f_vec acc0 == Loops.repeati (4 * n) f acc0)
let rec gf128_ni_repeati_extensionality n r f f_vec acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f_vec acc0;
    Loops.eq_repeati0 (4 * n) f acc0 end
  else begin
    gf128_ni_repeati_extensionality (n-1) r f f_vec acc0;
    let next_p = Loops.repeati (n-1) f_vec acc0 in
    let next_v = Loops.repeati (4*(n-1)) f acc0 in
    assert (next_p == next_v);

    let res1 = Loops.repeati n f_vec acc0 in
    let res2 = Loops.repeati (4*n) f acc0 in
    Loops.unfold_repeati n f_vec acc0 (n-1);
    assert (res1 == f_vec (n-1) next_p);

    Loops.unfold_repeati (4*n) f acc0 (4*n-4);
    Loops.unfold_repeati (4*n) f acc0 (4*n-3);
    Loops.unfold_repeati (4*n) f acc0 (4*n-2);
    Loops.unfold_repeati (4*n) f acc0 (4*n-1);
    assert (res2 == f (4*n-1) (f (4*n-2) (f (4*n-3) (f (4*n-4) next_p))))
  end

val gf128_update_multi_add_mul_lemma_aux:
  b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem -> r2:elem{r2 == fmul_be r r} -> r3:elem{r3 == fmul_be r r2} -> r4:elem{r4 == fmul_be r r3} ->
  Lemma (
    fmul_be b0 r4 `fadd` fmul_be b1 r3 `fadd` fmul_be b2 r2 `fadd` fmul_be b3 r ==
    fmul_be (fadd b3 (fmul_be (fadd b2 (fmul_be (fadd b1 (fmul_be b0 r)) r)) r)) r)
let gf128_update_multi_add_mul_lemma_aux b0 b1 b2 b3 r r2 r3 r4 = admit()

val gf128_add_zero: f:elem -> Lemma (fadd zero f == f)
let gf128_add_zero f = admit()

val gf128_add_commutativity: a:elem -> b:elem -> Lemma (fadd a b == fadd b a)
let gf128_add_commutativity a b = admit()

val gf128_update4_add_mul_lemma:
    pre:elem4
  -> b:lbytes 64
  -> acc:elem ->
  Lemma (
    let b0 = S.encode (Seq.slice b 0 16) in
    let b1 = S.encode (Seq.slice b 16 32) in
    let b2 = S.encode (Seq.slice b 32 48) in
    let b3 = S.encode (Seq.slice b 48 64) in

    gf128_update4_add_mul pre b acc ==
    fmul_be (b0 `fadd` acc) pre.[0] `fadd` fmul_be b1 pre.[1] `fadd` fmul_be b2 pre.[2] `fadd` fmul_be b3 pre.[3])
let gf128_update4_add_mul_lemma pre b acc =
  let acc1 = load_acc acc b in
  let b0 = S.encode (Seq.slice b 0 16) in
  let b1 = S.encode (Seq.slice b 16 32) in
  let b2 = S.encode (Seq.slice b 32 48) in
  let b3 = S.encode (Seq.slice b 48 64) in
  assert (acc1.[0] == fadd acc b0);
  gf128_add_zero b1;
  gf128_add_zero b2;
  gf128_add_zero b3;
  gf128_add_commutativity acc b0

val gf128_update_multi_add_mul_lemma:
    text:bytes{0 < length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi_add_mul text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)
let gf128_update_multi_add_mul_lemma text acc0 r = admit()
  // let len = length text in
  // let pre = load_precompute_r r in

  // let f = S.gf128_update1 r in
  // let f_vec = gf128_update4_add_mul pre in
  // let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
  // let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

  // let acc1 = repeat_blocks_multi #uint8 #elem 64 text f_vec acc0 in
  // lemma_repeat_blocks_multi #uint8 #elem 64 text f_vec acc0;
  // assert (acc1 == Loops.repeati (len / 64) repeat_bf_vec acc0);

  // let aux_repeat_bf (i:nat{i < len / 64}) (acc:elem) : Lemma
  //   (repeat_bf_vec i acc ==
  //    repeat_bf_sc (4*i+3) (repeat_bf_sc (4*i+2) (repeat_bf_sc (4*i+1) (repeat_bf_sc (4*i) acc)))) =

  //   let acc1 = repeat_bf_vec i acc in
  //   let b = Seq.slice text (i * 64) (i * 64 + 64) in
  //   assert (acc1 == gf128_update4_add_mul pre b acc);
  //   assert (acc1 == normalize4 (load_acc acc b) pre);
  //   let b0 = S.encode (Seq.slice text (i * 64) (i * 64 + 16)) in
  //   let b1 = S.encode (Seq.slice text (i * 64 + 16) (i * 64 + 32)) in
  //   let b2 = S.encode (Seq.slice text (i * 64 + 32) (i * 64 + 48)) in
  //   let b3 = S.encode (Seq.slice text (i * 64 + 48) (i * 64 + 64)) in

  //   gf128_update4_add_mul_lemma pre b acc;
  //   assert (acc1 == fmul_be (fadd b0 acc) pre.[0] `fadd` fmul_be b1 pre.[1] `fadd` fmul_be b2 pre.[2] `fadd` fmul_be b3 pre.[3]);
  //   let acc2 = repeat_bf_sc (4*i+3) (repeat_bf_sc (4*i+2) (repeat_bf_sc (4*i+1) (repeat_bf_sc (4*i) acc))) in
  //   //assert (acc2 == fmul_be (fadd b3 (fmul_be (fadd b2 (fmul_be (fadd b1 (fmul_be (fadd acc b0) r)) r)) r)) r);
  //   //gf128_update_multi_add_mul_lemma_aux (fadd b0 acc) b1 b2 b3 pre.[3] pre.[2] pre.[1] pre.[0];
  //   assume (acc2 == acc1) in

  // FStar.Classical.forall_intro_2 (aux_repeat_bf);
  // gf128_ni_repeati_extensionality (len / 64) r repeat_bf_sc repeat_bf_vec acc0;
  // assert (acc1 == Loops.repeati (len / 16) repeat_bf_sc acc0);
  // lemma_repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0

val gf128_update_multi_mul_add_lemma:
    text:bytes{0 < length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi_mul_add text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)
let gf128_update_multi_mul_add_lemma text acc0 r = admit()
  // let len = length text in
  // let f = S.gf128_update1 r in
  // let repeat_bf_t0 = repeat_blocks_f 16 text f (len / 16) in

  // let t0 = Seq.slice text 0 64 in
  // FStar.Seq.Base.lemma_len_slice text 0 64;
  // let t1 = Seq.slice text 64 len in
  // FStar.Seq.Base.lemma_len_slice text 64 len;

  // let acc1 = load_acc acc0 t0 in
  // let pre = load_precompute_r r in
  // let r4 = create 4 pre.[0] in
  // let f_vec = gf128_update4_mul_add r4 in
  // let acc2 = repeat_blocks_multi #uint8 #elem4 64 t1 f_vec acc1 in
  // let acc3 = normalize4 acc2 pre in
  // //assert (acc3 == gf128_update_multi_mul_add text acc0 r);
  // //poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  // assume (acc3 == repeat_blocks_multi #uint8 #elem 16 t1 f (normalize4 acc1 pre));
  // //poly_update_multi_lemma2 #w text acc0 r;
  // assume (acc3 == Loops.repeat_right 4 (len / 16) (Loops.fixed_a elem) repeat_bf_t0 (normalize4 acc1 pre));

  // // poly_update_multi_lemma1 #w text acc0 r;
  // assume (normalize4 (load_acc acc0 t0) pre == Loops.repeat_right 0 4 (Loops.fixed_a elem) repeat_bf_t0 acc0);
  // Loops.repeat_right_plus 0 4 (len / 16) (Loops.fixed_a elem) repeat_bf_t0 acc0;
  // assert (acc3 == Loops.repeat_right 0 (len / 16) (Loops.fixed_a elem) repeat_bf_t0 acc0);

  // Loops.repeati_def (len / 16) repeat_bf_t0 acc0;
  // lemma_repeat_blocks_multi #uint8 #elem 16 text f acc0;
  // assert (acc3 == repeat_blocks_multi #uint8 #elem 16 text f acc0)


val gf128_update_multi_lemma:
    alg:gf128_spec
  -> text:bytes{0 < length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi alg text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_lemma alg text acc0 r =
  match alg with
  | NI -> gf128_update_multi_add_mul_lemma text acc0 r
  | PreComp -> gf128_update_multi_mul_add_lemma text acc0 r


val gf128_update_vec_eq_lemma:
    alg:gf128_spec
  -> text:bytes
  -> acc0:elem
  -> r:elem ->
  Lemma (gf128_update_vec alg text acc0 r == S.gf128_update text acc0 r)

let gf128_update_vec_eq_lemma alg text acc0 r =
  let len = length text in
  let len0 = len / 64 * 64 in

  assert (len0 % 64 = 0);
  assert (len0 % 16 = 0);
  let t0 = Seq.slice text 0 len0 in
  let f = S.gf128_update1 r in
  let l = S.gf128_update_last r in

  if len0 > 0 then begin
    gf128_update_multi_lemma alg t0 acc0 r;
    PLoops.repeat_blocks_split #uint8 #elem 16 len0 text f l acc0 end
  else ()
