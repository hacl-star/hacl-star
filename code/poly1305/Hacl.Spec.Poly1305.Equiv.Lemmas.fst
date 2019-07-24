module Hacl.Spec.Poly1305.Equiv.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module Scalar = Spec.Poly1305
module Lemmas = Hacl.Spec.Poly1305.Lemmas

include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val poly_update_repeat_blocks_multi_lemma2_simplify:
  acc0:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem -> Lemma
    (pfadd (pfmul (pfadd (pfmul acc0 (pfmul r r)) c0) (pfmul r r)) (pfmul (pfadd (pfmul acc1 (pfmul r r)) c1) r) ==
    pfmul (pfadd (pfmul (pfadd (pfadd (pfmul acc0 (pfmul r r)) (pfmul acc1 r)) c0) r) c1) r)
let poly_update_repeat_blocks_multi_lemma2_simplify acc0 acc1 c0 c1 r =
  Lemmas.poly_update_repeat_blocks_multi_lemma2_simplify acc0 acc1 c0 c1 r

val poly_update_repeat_blocks_multi_lemma4_simplify:
    a0r4:pfelem -> a1:pfelem -> a2:pfelem -> a3:pfelem
  -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem
  -> r:pfelem ->
  Lemma
   (pfadd (pfadd (pfadd
     (pfmul (pfadd a0r4 c0) (pfmul (pfmul r r) (pfmul r r)))
     (pfmul (pfadd (pfmul a1 (pfmul (pfmul r r) (pfmul r r))) c1) (pfmul (pfmul r r) r)))
     (pfmul (pfadd (pfmul a2 (pfmul (pfmul r r) (pfmul r r))) c2) (pfmul r r)))
     (pfmul (pfadd (pfmul a3 (pfmul (pfmul r r) (pfmul r r))) c3) r) ==
    pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfadd (pfadd (pfadd a0r4
	  (pfmul a1 (pfmul (pfmul r r) r))) (pfmul a2 (pfmul r r))) (pfmul a3 r)) c0) r) c1) r) c2) r) c3) r)
let poly_update_repeat_blocks_multi_lemma4_simplify a0r4 a1 a2 a3 c0 c1 c2 c3 r =
  Lemmas.poly_update_repeat_blocks_multi_lemma4_simplify a0r4 a1 a2 a3 c0 c1 c2 c3 r

val poly_update_multi_lemma_load2_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem ->
  Lemma
    (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r ==
     pfadd (pfmul (pfadd acc0 c0) (pfmul r r)) (pfmul c1 r))
let poly_update_multi_lemma_load2_simplify acc0 r c0 c1 =
  Lemmas.poly_update_multi_lemma_load2_simplify acc0 r c0 c1

val poly_update_multi_lemma_load4_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem ->
  Lemma
   (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r) c2) r) c3) r ==
     pfadd (pfadd (pfadd (pfmul (pfadd acc0 c0) (pfmul (pfmul r r) (pfmul r r)))
      (pfmul c1 (pfmul (pfmul r r) r))) (pfmul c2 (pfmul r r))) (pfmul c3 r))
let poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3 =
  Lemmas.poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3

//
// Lemma
// (normalize_n #w (repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (poly1305_update_nblocks #w (compute_rw #w r)) acc) r ==
//  repeat_blocks_multi #uint8 #pfelem size_block text (Scalar.poly1305_update1 r size_block) (normalize_n #w acc r))
//

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -Hacl.Spec.Poly1305.Lemmas'"

val repeat_w:
    w:lanes
  -> n:nat
  -> f:(i:nat{i < w * n} -> pfelem -> pfelem)
  -> i:nat{i < n}
  -> acc:pfelem ->
  Tot pfelem
let repeat_w w n f i acc =
  match w with
  | 1 -> f i acc
  | 2 -> f (2*i+1) (f (2*i) acc)
  | 4 -> f (4*i+3) (f (4*i+2) (f (4*i+1) (f (4*i) acc)))

val unfold_w:
    w:lanes
  -> n:pos
  -> f:(i:nat{i < w * n} -> pfelem -> pfelem)
  -> acc0:pfelem ->
  Lemma (Loops.repeati (w*n) f acc0 == repeat_w w n f (n-1) (Loops.repeati (w*(n-1)) f acc0))
let unfold_w w n f acc =
  match w with
  | 1 ->
    Loops.unfold_repeati n f acc (n-1)
  | 2 ->
    Loops.unfold_repeati (2*n) f acc (2*n-2);
    Loops.unfold_repeati (2*n) f acc (2*n-1)
  | 4 ->
    Loops.unfold_repeati (4*n) f acc (4*n-4);
    Loops.unfold_repeati (4*n) f acc (4*n-3);
    Loops.unfold_repeati (4*n) f acc (4*n-2);
    Loops.unfold_repeati (4*n) f acc (4*n-1)

#set-options "--z3rlimit 150 --max_fuel 2"

val normalizen_repeati_extensionality:
    w:lanes
  -> n:nat
  -> r:pfelem
  -> f:(i:nat{i < n * w} -> pfelem -> pfelem)
  -> f_vec:(i:nat{i < n} -> elem w -> elem w)
  -> acc0_vec:elem w ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_vec:elem w). normalize_n (f_vec i acc_vec) r == repeat_w w n f i (normalize_n acc_vec r)))
  (ensures (normalize_n (Loops.repeati n f_vec acc0_vec) r == Loops.repeati (w * n) f (normalize_n acc0_vec r)))

let rec normalizen_repeati_extensionality w n r f f_vec acc0_vec =
  if n = 0 then begin
    Loops.eq_repeati0 n f_vec acc0_vec;
    Loops.eq_repeati0 (w * n) f (normalize_n acc0_vec r) end
  else begin
    let acc0 = normalize_n acc0_vec r in
    normalizen_repeati_extensionality w (n-1) r f f_vec acc0_vec;
    let next_p = Loops.repeati (n-1) f_vec acc0_vec in
    let next_v = Loops.repeati (w*(n-1)) f acc0 in
    assert (normalize_n next_p r == next_v);

    let res1 = Loops.repeati n f_vec acc0_vec in
    let res2 = Loops.repeati (w*n) f acc0 in
    Loops.unfold_repeati n f_vec acc0_vec (n-1);
    assert (res1 == f_vec (n-1) next_p);
    unfold_w w n f acc0;
    assert (res2 == repeat_w w n f (n-1) next_v);
    assert (normalize_n res1 r == res2)
  end

val poly_update_repeat_blocks_multi_lemma1:
    text:bytes{length text % Scalar.size_block = 0}
  -> acc:elem 1
  -> r:pfelem ->
  Lemma
    (normalize_1 (repeat_blocks_multi #uint8 #(elem 1) size_block text (poly1305_update_nblocks #1 (compute_rw #1 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (Scalar.poly1305_update1 r size_block) (normalize_1 acc r))
let poly_update_repeat_blocks_multi_lemma1 text acc_vec0 r =
  let len = length text in

  let nb_vec = len / size_block in
  let nb = len / size_block in

  let f_vec = poly1305_update_nblocks #1 (compute_rw #1 r) in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_vec = repeat_blocks_f size_block text f_vec nb_vec in
  let repeat_bf_sc = repeat_blocks_f size_block text f nb in

  let acc_vec1 = repeat_blocks_multi #uint8 #(elem 1) size_block text f_vec acc_vec0 in
  lemma_repeat_blocks_multi #uint8 #(elem 1) size_block text f_vec acc_vec0;
  assert (acc_vec1 == Loops.repeati nb_vec repeat_bf_vec acc_vec0);
  let acc1 = normalize_1 acc_vec1 r in

  let acc0 = normalize_1 acc_vec0 r in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block text f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block text f acc0;
  assert (acc2 == Loops.repeati nb repeat_bf_sc acc0);

  assert (nb == nb_vec);
  let aux_repeat_bf (i:nat{i < nb_vec}) (acc_vec0:elem 1) : Lemma
    (normalize_1 (repeat_bf_vec i acc_vec0) r ==
     repeat_bf_sc i (normalize_1 acc_vec0 r))
    = () in

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  normalizen_repeati_extensionality 1 nb_vec r repeat_bf_sc repeat_bf_vec acc_vec0

val poly_update_repeat_blocks_multi_lemma2:
    text:bytes{length text % (2 * size_block) = 0}
  -> acc:elem 2
  -> r:pfelem ->
  Lemma
    (normalize_2 (repeat_blocks_multi #uint8 #(elem 2) (2 * size_block) text (poly1305_update_nblocks #2 (compute_rw #2 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (Scalar.poly1305_update1 r size_block) (normalize_2 acc r))
let poly_update_repeat_blocks_multi_lemma2 text acc_vec0 r =
  let len = length text in

  let nb_vec = len / (2 * size_block) in
  let nb = len / size_block in

  let f_vec = poly1305_update_nblocks #2 (compute_rw #2 r) in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_vec = repeat_blocks_f (2 * size_block) text f_vec nb_vec in
  let repeat_bf_sc = repeat_blocks_f size_block text f nb in

  let acc_vec1 = repeat_blocks_multi #uint8 #(elem 2) (2 * size_block) text f_vec acc_vec0 in
  lemma_repeat_blocks_multi #uint8 #(elem 2) (2 * size_block) text f_vec acc_vec0;
  assert (acc_vec1 == Loops.repeati nb_vec repeat_bf_vec acc_vec0);
  let acc1 = normalize_2 acc_vec1 r in

  let acc0 = normalize_2 acc_vec0 r in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block text f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block text f acc0;
  assert (acc2 == Loops.repeati nb repeat_bf_sc acc0);

  assert (nb == 2 * nb_vec);
  let aux_repeat_bf (i:nat{i < nb_vec}) (acc_vec0:elem 2) : Lemma
    (normalize_2 (repeat_bf_vec i acc_vec0) r ==
     repeat_bf_sc (2*i+1) (repeat_bf_sc (2*i) (normalize_2 acc_vec0 r)))
    =
      let acc_vec1 = repeat_bf_vec i acc_vec0 in
      assert (acc_vec1 == poly1305_update_nblocks #2 (compute_rw #2 r) (Seq.slice text (i * 32) (i * 32 + 32)) acc_vec0);
      let rw = compute_rw #2 r in
      let b0 = Seq.slice text (i * 32) (i * 32 + 16) in
      let b1 = Seq.slice text (i * 32 + 16) (i * 32 + 32) in
      let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
      let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in

      let acc3 = normalize_2 acc_vec1 r in
      let acc0 = normalize_2 acc_vec0 r in
      let acc1 = repeat_bf_sc (2*i) acc0 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b0) acc0 prime;
      let acc2 = repeat_bf_sc (2*i+1) acc1 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b1) acc1 prime;
      poly_update_repeat_blocks_multi_lemma2_simplify acc_vec0.[0] acc_vec0.[1] c0 c1 r;
      assert (acc2 == acc3)
  in

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  normalizen_repeati_extensionality 2 nb_vec r repeat_bf_sc repeat_bf_vec acc_vec0;
  assert (normalize_2 (Loops.repeati nb_vec repeat_bf_vec acc_vec0) r == Loops.repeati nb repeat_bf_sc (normalize_2 acc_vec0 r));
  assert (normalize_2 acc_vec1 r == acc2)

#set-options "--max_fuel 0"

val poly_update_repeat_blocks_multi_lemma4:
    text:bytes{length text % (4 * size_block) = 0}
  -> acc:elem 4
  -> r:pfelem ->
  Lemma
    (normalize_4 (repeat_blocks_multi #uint8 #(elem 4) (4 * size_block) text (poly1305_update_nblocks #4 (compute_rw #4 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (Scalar.poly1305_update1 r size_block) (normalize_4 acc r))
let poly_update_repeat_blocks_multi_lemma4 text acc_vec0 r =
  let len = length text in

  let nb_vec = len / (4 * size_block) in
  let nb = len / size_block in

  let f_vec = poly1305_update_nblocks #4 (compute_rw #4 r) in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_vec = repeat_blocks_f (4 * size_block) text f_vec nb_vec in
  let repeat_bf_sc = repeat_blocks_f size_block text f nb in

  let acc_vec1 = repeat_blocks_multi #uint8 #(elem 4) (4 * size_block) text f_vec acc_vec0 in
  lemma_repeat_blocks_multi #uint8 #(elem 4) (4 * size_block) text f_vec acc_vec0;
  assert (acc_vec1 == Loops.repeati nb_vec repeat_bf_vec acc_vec0);
  let acc1 = normalize_4 acc_vec1 r in

  let acc0 = normalize_4 acc_vec0 r in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block text f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block text f acc0;
  assert (acc2 == Loops.repeati nb repeat_bf_sc acc0);

  assert (nb == 4 * nb_vec);
  let aux_repeat_bf (i:nat{i < nb_vec}) (acc_vec0:elem 4) : Lemma
    (normalize_4 (repeat_bf_vec i acc_vec0) r ==
     repeat_bf_sc (4*i+3) (repeat_bf_sc (4*i+2) (repeat_bf_sc (4*i+1) (repeat_bf_sc (4*i) (normalize_4 acc_vec0 r)))))
    =
      let acc_vec1 = repeat_bf_vec i acc_vec0 in
      assert (acc_vec1 == poly1305_update_nblocks #4 (compute_rw #4 r) (Seq.slice text (i * 64) (i * 64 + 64)) acc_vec0);
      let rw = compute_rw #4 r in
      let b0 = Seq.slice text (i * 64) (i * 64 + 16) in
      let b1 = Seq.slice text (i * 64 + 16) (i * 64 + 32) in
      let b2 = Seq.slice text (i * 64 + 32) (i * 64 + 48) in
      let b3 = Seq.slice text (i * 64 + 48) (i * 64 + 64) in
      let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
      let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
      let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
      let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in
      let r2 = pfmul r r in
      let r4 = pfmul r2 r2 in
      let acc5 = normalize_4 acc_vec1 r in

      let acc0 = normalize_4 acc_vec0 r in
      let acc1 = repeat_bf_sc (4*i) acc0 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b0) acc0 prime;
      let acc2 = repeat_bf_sc (4*i+1) acc1 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b1) acc1 prime;
      let acc3 = repeat_bf_sc (4*i+2) acc2 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b2) acc2 prime;
      let acc4 = repeat_bf_sc (4*i+3) acc3 in
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b3) acc3 prime;
      poly_update_repeat_blocks_multi_lemma4_simplify
	(pfmul acc_vec0.[0] r4) acc_vec0.[1] acc_vec0.[2] acc_vec0.[3] c0 c1 c2 c3 r;
      assert (acc5 == acc4)
  in

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  normalizen_repeati_extensionality 4 nb_vec r repeat_bf_sc repeat_bf_vec acc_vec0;
  assert (normalize_4 (Loops.repeati nb_vec repeat_bf_vec acc_vec0) r == Loops.repeati nb repeat_bf_sc (normalize_4 acc_vec0 r));
  assert (acc1 == acc2)
  
val normalize_4_lemma: acc:elem 4 -> r:pfelem -> Lemma
  (normalize_4 acc r ==
    pfadd (pfadd (pfadd (pfmul acc.[0] (pfmul (pfmul r r) (pfmul r r)))
      (pfmul acc.[1] (pfmul (pfmul r r) r))) (pfmul acc.[2] (pfmul r r))) (pfmul acc.[3] r))
let normalize_4_lemma acc r = ()

//
// Lemma
//  (normalize_n #w (load_acc #w acc0 (Seq.slice text 0 (w * size_block))) r ==
//    repeat_blocks_multi #uint8 #pfelem size_block (Seq.slice text 0 (w * size_block)) (update1 r size_block) acc0)
//

val poly_update_multi_lemma_load1:
    text:bytes{0 < length text /\ length text % size_block = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 size_block in
    let acc1 = load_acc #1 acc0 t0 in
    normalize_1 acc1 r ==
      repeat_blocks_multi #uint8 #pfelem size_block t0 (Scalar.poly1305_update1 r size_block) acc0)
let poly_update_multi_lemma_load1 text acc0 r =
  let t0 = Seq.slice text 0 size_block in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f 1 in

  let acc1 = load_acc #1 acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0;
  assert (acc2 == Loops.repeati 1 repeat_bf_s0 acc0);

  Loops.unfold_repeati 1 repeat_bf_s0 acc0 0;
  Loops.eq_repeati0 1 repeat_bf_s0 acc0

val poly_update_multi_lemma_load2:
    text:bytes{0 < length text /\ length text % (2 * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
    (let t0 = Seq.slice text 0 (2 * size_block) in
    let acc1 = load_acc #2 acc0 t0 in
    normalize_2 acc1 r ==
      repeat_blocks_multi #uint8 #pfelem size_block t0 (Scalar.poly1305_update1 r size_block) acc0)
let poly_update_multi_lemma_load2 text acc0 r =
  let t0 = Seq.slice text 0 (2 * size_block) in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f 2 in

  let acc1 = load_acc #2 acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0;
  assert (acc2 == Lib.LoopCombinators.repeati 2 repeat_bf_s0 acc0);

  Lib.LoopCombinators.unfold_repeati 2 repeat_bf_s0 acc0 1;
  Lib.LoopCombinators.unfold_repeati 2 repeat_bf_s0 acc0 0;
  Lib.LoopCombinators.eq_repeati0 2 repeat_bf_s0 acc0;

  assert (acc2 == repeat_bf_s0 1 (repeat_bf_s0 0 acc0));
  assert (acc2 ==
    Scalar.poly1305_update1 r size_block (Seq.slice text size_block (2 * size_block))
      (Scalar.poly1305_update1 r size_block (Seq.slice text 0 size_block) acc0));

  let b0 = Seq.slice text 0 size_block in
  let b1 = Seq.slice text size_block (2 * size_block) in

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b0) acc0 prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b1)
    (Scalar.poly1305_update1 r size_block b0 acc0) prime;

  assert (acc2 == pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r);

  let acc3 = normalize_2 acc1 r in
  assert (acc3 == pfadd (pfmul acc1.[0] (pfmul r r)) (pfmul acc1.[1] r));
  assert (acc1.[0] == pfadd acc0 c0);
  assert (acc1.[1] == pfadd 0 c1);
  FStar.Math.Lemmas.modulo_lemma c1 Scalar.prime;
  assert (acc1.[1] == c1);

  assert (acc3 == pfadd (pfmul (pfadd acc0 c0) (pfmul r r)) (pfmul c1 r));
  poly_update_multi_lemma_load2_simplify acc0 r c0 c1;
  assert (acc2 == acc3)

val poly_update_multi_lemma_load4:
    text:bytes{0 < length text /\ length text % (4 * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (4 * size_block) in
    let acc1 = load_acc #4 acc0 t0 in
    normalize_4 acc1 r == repeat_blocks_multi #uint8 #pfelem size_block t0 (Scalar.poly1305_update1 r size_block) acc0)
let poly_update_multi_lemma_load4 text acc0 r =
  let t0 = Seq.slice text 0 (4 * size_block) in
  let f = Scalar.poly1305_update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f 4 in

  let acc1 = load_acc #4 acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0 in
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0;
  assert (acc2 == Lib.LoopCombinators.repeati 4 repeat_bf_s0 acc0);

  Lib.LoopCombinators.unfold_repeati 4 repeat_bf_s0 acc0 3;
  Lib.LoopCombinators.unfold_repeati 4 repeat_bf_s0 acc0 2;
  Lib.LoopCombinators.unfold_repeati 4 repeat_bf_s0 acc0 1;
  Lib.LoopCombinators.unfold_repeati 4 repeat_bf_s0 acc0 0;
  Lib.LoopCombinators.eq_repeati0 4 repeat_bf_s0 acc0;

  assert (acc2 == repeat_bf_s0 3 (repeat_bf_s0 2 (repeat_bf_s0 1 (repeat_bf_s0 0 acc0))));
  assert (acc2 ==
  Scalar.poly1305_update1 r size_block (Seq.slice text (3 * size_block) (4 * size_block))
    (Scalar.poly1305_update1 r size_block (Seq.slice text (2 * size_block) (3 * size_block))
      (Scalar.poly1305_update1 r size_block (Seq.slice text size_block (2 * size_block))
	(Scalar.poly1305_update1 r size_block (Seq.slice text 0 size_block) acc0))));

  let b0 = Seq.slice text 0 size_block in
  let b1 = Seq.slice text size_block (2 * size_block) in
  let b2 = Seq.slice text (2 * size_block) (3 * size_block) in
  let b3 = Seq.slice text (3 * size_block) (4 * size_block) in

  let acc2_0 = Scalar.poly1305_update1 r size_block b0 acc0 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b0) acc0 prime;
  let acc2_1 = Scalar.poly1305_update1 r size_block b1 acc2_0 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b1) acc2_0 prime;
  let acc2_2 = Scalar.poly1305_update1 r size_block b2 acc2_1 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b2) acc2_1 prime;
  let acc2_3 = Scalar.poly1305_update1 r size_block b3 acc2_2 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (pow2 128 + nat_from_bytes_le b3) acc2_2 prime;

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
  let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in
  assert (acc2 ==
    pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r) c2) r) c3) r);

  let acc3 = normalize_4 acc1 r in
  assert (acc1.[0] == pfadd acc0 c0);
  FStar.Math.Lemmas.modulo_lemma c1 Scalar.prime;
  FStar.Math.Lemmas.modulo_lemma c2 Scalar.prime;
  FStar.Math.Lemmas.modulo_lemma c3 Scalar.prime;
  assert (acc1.[1] == c1);
  assert (acc1.[2] == c2);
  assert (acc1.[3] == c3);
  assert (acc3 ==
    pfadd (pfadd (pfadd (pfmul (pfadd acc0 c0) (pfmul (pfmul r r) (pfmul r r)))
      (pfmul c1 (pfmul (pfmul r r) r))) (pfmul c2 (pfmul r r))) (pfmul c3 r));
  poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3;
  assert (acc2 == acc3)
