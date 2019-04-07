module Hacl.Spec.Poly1305.Equiv.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module S = Spec.Poly1305
include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1"

val lemma_mod_add_distr_twice: a:nat -> b:nat -> n:pos -> Lemma
  ((a % n + b % n) % n == (a + b) % n)
let lemma_mod_add_distr_twice a b n =
  FStar.Math.Lemmas.lemma_mod_add_distr a b n;
  FStar.Math.Lemmas.lemma_mod_add_distr (b % n) a n

val lemma_mod_mul_distr_twice: a:nat -> b:nat -> n:pos -> Lemma
  (((a % n) * (b % n)) % n == (a * b) % n)
let lemma_mod_mul_distr_twice a b n =
  FStar.Math.Lemmas.lemma_mod_mul_distr_l a (b % n) n;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r a b n

val lemma_mod_add_mul_distr: a:nat -> b:nat -> c:nat -> n:pos -> Lemma
  ((a * (b % n) + c) % n == (a * b + c) % n)
let lemma_mod_add_mul_distr a b c n =
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (a * (b % n)) c n;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r a b n;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (a * b) c n

val poly_update_repeat_blocks_multi_lemma2_simplify_lp:
  a0r2:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem -> r2:nat{r2 == r * r} -> Lemma
  (((((a0r2 + c0) % prime) * (r2 % prime) % prime) + (((((acc1 * (r2 % prime)) % prime) + c1) % prime) * r % prime)) % prime ==
  (a0r2 * r2 + c0 * r2 + acc1 * r2 * r + c1 * r) % prime)
let poly_update_repeat_blocks_multi_lemma2_simplify_lp a0r2 acc1 c0 c1 r r2 =
  let lp = ((((a0r2 + c0) % prime) * (r2 % prime) % prime) + (((((acc1 * (r2 % prime)) % prime) + c1) % prime) * r % prime)) % prime in
  calc (==) {
    ((((a0r2 + c0) % prime) * (r2 % prime) % prime) + (((((acc1 * (r2 % prime)) % prime) + c1) % prime) * r % prime)) % prime;
  (==) { lemma_mod_mul_distr_twice (a0r2 + c0) r2 prime }
    (((a0r2 + c0) * r2 % prime) + (((((acc1 * (r2 % prime)) % prime) + c1) % prime) * r % prime)) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r acc1 r2 prime }
    (((a0r2 + c0) * r2 % prime) + (((((acc1 * r2) % prime) + c1) % prime) * r % prime)) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l (acc1 * r2) c1 prime }
    (((a0r2 + c0) * r2 % prime) + (((acc1 * r2 + c1) % prime) * r % prime)) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l (acc1 * r2 + c1) r prime }
    (((a0r2 + c0) * r2 % prime) + ((acc1 * r2 + c1) * r % prime)) % prime;
  (==) { lemma_mod_add_distr_twice ((a0r2 + c0) * r2) ((acc1 * r2 + c1) * r) prime }
    ((a0r2 + c0) * r2 + (acc1 * r2 + c1) * r) % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left a0r2 c0 r2 }
    (a0r2 * r2 + c0 * r2 + (acc1 * r2 + c1) * r) % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left (acc1 * r2) c1 r }
    (a0r2 * r2 + c0 * r2 + acc1 * r2 * r + c1 * r) % prime;
  };
  assert (lp == (a0r2 * r2 + c0 * r2 + acc1 * r2 * r + c1 * r) % prime)

val poly_update_repeat_blocks_multi_lemma2_simplify_rp:
  a0r2:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem -> r2:nat{r2 == r * r} -> Lemma
  (((((((a0r2 + (acc1 * r % prime)) % prime) + c0) % prime) * r % prime) + c1) % prime * r % prime ==
   (a0r2 * r2 + c0 * r2 + acc1 * r2 * r + c1 * r) % prime)
let poly_update_repeat_blocks_multi_lemma2_simplify_rp a0r2 acc1 c0 c1 r r2 =
  calc (==) {
    ((((((a0r2 + (acc1 * r % prime)) % prime) + c0) % prime) * r % prime) + c1) % prime * r % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r a0r2 (acc1 * r) prime }
    ((((((a0r2 + acc1 * r) % prime) + c0) % prime) * r % prime) + c1) % prime * r % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l (a0r2 + acc1 * r) c0 prime }
    ((((a0r2 + acc1 * r + c0) % prime) * r % prime) + c1) % prime * r % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l (a0r2 + acc1 * r + c0) r prime }
    (((a0r2 + acc1 * r + c0) * r % prime) + c1) % prime * r % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l ((a0r2 + acc1 * r + c0) * r) c1 prime }
    ((a0r2 + acc1 * r + c0) * r + c1) % prime * r % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l ((a0r2 + acc1 * r + c0) * r + c1) r prime }
    ((a0r2 + acc1 * r + c0) * r + c1) * r % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left ((a0r2 + acc1 * r + c0) * r) c1 r }
    ((a0r2 + acc1 * r + c0) * r * r + c1 * r) % prime;
  (==) { FStar.Math.Lemmas.paren_mul_right (a0r2 + acc1 * r + c0) r r }
    ((a0r2 + acc1 * r + c0) * (r * r) + c1 * r) % prime;
  (==) { assert (r * r == r2) }
    ((a0r2 + acc1 * r + c0) * r2 + c1 * r) % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left (a0r2 + acc1 * r) c0 r2 }
    ((a0r2 + acc1 * r) * r2 + c0 * r2 + c1 * r) % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left a0r2 (acc1 * r) r2 }
    (a0r2 * r2 + acc1 * r * r2 + c0 * r2 + c1 * r) % prime;
  (==) { FStar.Math.Lemmas.paren_mul_right acc1 r r2 }
    (a0r2 * r2 + acc1 * (r2 * r) + c0 * r2 + c1 * r) % prime;
  (==) { FStar.Math.Lemmas.paren_mul_right acc1 r2 r }
    (a0r2 * r2 + acc1 * r2 * r + c0 * r2 + c1 * r) % prime;
    }

val poly_update_repeat_blocks_multi_lemma2_simplify:
  acc0:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem -> Lemma
    (pfadd (pfmul (pfadd (pfmul acc0 (pfmul r r)) c0) (pfmul r r)) (pfmul (pfadd (pfmul acc1 (pfmul r r)) c1) r) ==
    pfmul (pfadd (pfmul (pfadd (pfadd (pfmul acc0 (pfmul r r)) (pfmul acc1 r)) c0) r) c1) r)
let poly_update_repeat_blocks_multi_lemma2_simplify acc0 acc1 c0 c1 r =
  let a0r2 = pfmul acc0 (pfmul r r) in
  let r2 = r * r in
  poly_update_repeat_blocks_multi_lemma2_simplify_lp a0r2 acc1 c0 c1 r r2;
  poly_update_repeat_blocks_multi_lemma2_simplify_rp a0r2 acc1 c0 c1 r r2

val poly_update_multi_lemma_load2_simplify_lp:
  a0:pfelem -> r0:pfelem -> c0:pfelem -> c1:pfelem -> Lemma
  ((((a0 * r0 % prime) + c1) % prime) * r0 % prime == (a0 * r0 * r0 + c1 * r0) % prime)
let poly_update_multi_lemma_load2_simplify_lp a0 r0 c0 c1 =
  calc (==) {
    (((a0 * r0 % prime) + c1) % prime) * r0 % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l (a0 * r0) c1 prime }
    ((a0 * r0 + c1) % prime) * r0 % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l (a0 * r0 + c1) r0 prime }
    (a0 * r0 + c1) * r0 % prime;
  (==) { FStar.Math.Lemmas.distributivity_add_left (a0 * r0) c1 r0 }
    (a0 * r0 * r0 + c1 * r0) % prime;
  }

val poly_update_multi_lemma_load2_simplify_rp:
  a0:pfelem -> r0:pfelem -> c0:pfelem -> c1:pfelem -> Lemma
  (((a0 * (r0 * r0 % prime) % prime) + (c1 * r0 % prime)) % prime == (a0 * r0 * r0 + c1 * r0) % prime)
let poly_update_multi_lemma_load2_simplify_rp a0 r0 c0 c1 =
  calc (==) {
    ((a0 * (r0 * r0 % prime) % prime) + (c1 * r0 % prime)) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r a0 (r0 * r0) prime }
    ((a0 * (r0 * r0) % prime) + (c1 * r0 % prime)) % prime;
  (==) { FStar.Math.Lemmas.paren_mul_right a0 r0 r0 }
    ((a0 * r0 * r0 % prime) + (c1 * r0 % prime)) % prime;
  (==) { lemma_mod_add_distr_twice (a0 * r0 * r0) (c1 * r0) prime }
    (a0 * r0 * r0 + c1 * r0) % prime;
   }

val poly_update_multi_lemma_load2_simplify:
  acc0:pfelem -> r0:pfelem -> c0:pfelem -> c1:pfelem ->
  Lemma
    (pfmul (pfadd (pfmul (pfadd acc0 c0) r0) c1) r0 ==
     pfadd (pfmul (pfadd acc0 c0) (pfmul r0 r0)) (pfmul c1 r0))
let poly_update_multi_lemma_load2_simplify acc0 r0 c0 c1 =
  let a0 = pfadd acc0 c0 in
  poly_update_multi_lemma_load2_simplify_lp a0 r0 c0 c1;
  poly_update_multi_lemma_load2_simplify_rp a0 r0 c0 c1

//
// Lemma
// (normalize_n #w (repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (updaten #w (compute_rw #w r)) acc) r ==
//  repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) (normalize_n #w acc r))
//

#set-options "--max_fuel 2"

val poly_update_repeat_blocks_multi_lemma1:
    text:bytes{length text % size_block = 0}
  -> acc:elem 1
  -> r:pfelem ->
  Lemma
    (normalize_1 (repeat_blocks_multi #uint8 #(elem 1) size_block text (updaten #1 (compute_rw #1 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) (normalize_1 acc r))
let poly_update_repeat_blocks_multi_lemma1 text acc_vec0 r =
  let len = length text in

  let nb_vec = len / size_block in
  let nb = len / size_block in

  let f_vec = updaten #1 (compute_rw #1 r) in
  let f = update1 r size_block in
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
  let rec aux (n:nat{n <= nb_vec}) : Lemma
    (normalize_1 (Loops.repeati n repeat_bf_vec acc_vec0) r ==
     Loops.repeati n repeat_bf_sc acc0) =
    if n = 0 then (
      Loops.eq_repeati0 n repeat_bf_vec acc_vec0;
      Loops.eq_repeati0 n repeat_bf_sc acc0;
      assert (normalize_1 acc_vec0 r == acc0)
    ) else (
      Loops.unfold_repeati n repeat_bf_vec acc_vec0 (n-1);
      Loops.unfold_repeati n repeat_bf_sc acc0 (n-1);
      aux (n-1);
      let next_p = Loops.repeati (n-1) repeat_bf_vec acc_vec0 in
      let next_v = Loops.repeati (n-1) repeat_bf_sc acc0 in
      assert (normalize_1 next_p r == next_v);
      let res1 = Loops.repeati n repeat_bf_vec acc_vec0 in
      let res2 = Loops.repeati n repeat_bf_sc acc0 in
      assert (res1 == repeat_bf_vec (n-1) next_p);
      assert (res2 == repeat_bf_sc (n-1) next_v);
      assert (normalize_1 res1 r == res2)
    )
  in aux nb_vec

val poly_update_repeat_blocks_multi_lemma2:
    text:bytes{length text % (2 * size_block) = 0}
  -> acc:elem 2
  -> r:pfelem ->
  Lemma
    (normalize_2 (repeat_blocks_multi #uint8 #(elem 2) (2 * size_block) text (updaten #2 (compute_rw #2 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) (normalize_2 acc r))
let poly_update_repeat_blocks_multi_lemma2 text acc_vec0 r =
  let len = length text in

  let nb_vec = len / (2 * size_block) in
  let nb = len / size_block in

  let f_vec = updaten #2 (compute_rw #2 r) in
  let f = update1 r size_block in
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
      assert (acc_vec1 == updaten #2 (compute_rw #2 r) (Seq.slice text (i * 32) (i * 32 + 32)) acc_vec0);
      let rw = compute_rw #2 r in
      let b0 = Seq.slice text (i * 32) (i * 32 + size_block) in
      let b1 = Seq.slice text (i * 32 + size_block) (i * 32 + 32) in
      let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
      let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in

      let acc3 = normalize_2 acc_vec1 r in

      let acc0 = normalize_2 acc_vec0 r in
      let acc1 = repeat_bf_sc (2*i) acc0 in
      let acc2 = repeat_bf_sc (2*i+1) acc1 in
      poly_update_repeat_blocks_multi_lemma2_simplify acc_vec0.[0] acc_vec0.[1] c0 c1 r;
      assert (acc2 == acc3)
  in

  let rec aux (n:nat{n <= nb_vec}) : Lemma
    (normalize_2 (Loops.repeati n repeat_bf_vec acc_vec0) r ==
     Loops.repeati (2 * n) repeat_bf_sc acc0) =
    if n = 0 then (
      Loops.eq_repeati0 n repeat_bf_vec acc_vec0;
      Loops.eq_repeati0 (2 * n) repeat_bf_sc acc0;
      assert (normalize_2 acc_vec0 r == acc0)
    ) else (
      Loops.unfold_repeati n repeat_bf_vec acc_vec0 (n-1);
      Loops.unfold_repeati (2*n) repeat_bf_sc acc0 (2*(n-1));
      Loops.unfold_repeati (2*n) repeat_bf_sc acc0 (2*n-1);
      aux (n-1);
      let next_p = Loops.repeati (n-1) repeat_bf_vec acc_vec0 in
      let next_v = Loops.repeati (2*(n-1)) repeat_bf_sc acc0 in
      assert (normalize_2 next_p r == next_v);
      let res1 = Loops.repeati n repeat_bf_vec acc_vec0 in
      let res2 = Loops.repeati (2*n) repeat_bf_sc acc0 in
      assert (res1 == repeat_bf_vec (n-1) next_p);
      assert (res2 == repeat_bf_sc (2*n-1) (repeat_bf_sc (2*(n-1)) next_v));
      aux_repeat_bf (n-1) next_p;
      assert (normalize_2 res1 r == res2)
    )
  in aux nb_vec

#reset-options "--z3rlimit 150 --max_fuel 2"

val poly_update_repeat_blocks_multi_lemma4:
    text:bytes{length text % (4 * size_block) = 0}
  -> acc:elem 4
  -> r:pfelem ->
  Lemma
    (normalize_4 (repeat_blocks_multi #uint8 #(elem 4) (4 * size_block) text (updaten #4 (compute_rw #4 r)) acc) r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) (normalize_4 acc r))
let poly_update_repeat_blocks_multi_lemma4 text acc r = admit()

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
      repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0)
let poly_update_multi_lemma_load1 text acc0 r =
  let t0 = Seq.slice text 0 size_block in
  let f = update1 r size_block in
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
      repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0)
let poly_update_multi_lemma_load2 text acc0 r =
  let t0 = Seq.slice text 0 (2 * size_block) in
  let f = update1 r size_block in
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
    update1 r size_block (Seq.slice text size_block (2 * size_block))
      (update1 r size_block (Seq.slice text 0 size_block) acc0));

  let b0 = Seq.slice text 0 size_block in
  let b1 = Seq.slice text size_block (2 * size_block) in

  let acc2_0 = update1 r size_block b0 acc0 in
  assert (acc2 == update1 r size_block b1 acc2_0);
  assert (acc2_0 == pfmul (pfadd acc0 (pfadd (pow2 128) (nat_from_bytes_le b0))) r);
  assert (acc2 == pfmul (pfadd acc2_0 (pfadd (pow2 128) (nat_from_bytes_le b1))) r);

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  assert (acc2 == pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r);

  let acc3 = normalize_2 acc1 r in
  assert (acc3 == pfadd (pfmul acc1.[0] (pfmul r r)) (pfmul acc1.[1] r));
  assert (acc1.[0] == pfadd acc0 (pfadd (pow2 128) (nat_from_bytes_le b0)));
  assert (acc1.[1] == pfadd 0 (pfadd (pow2 128) (nat_from_bytes_le b1)));
  FStar.Math.Lemmas.modulo_lemma (pfadd (pow2 128) (nat_from_bytes_le b1)) prime;
  assert (acc1.[1] == pfadd (pow2 128) (nat_from_bytes_le b1));

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
    normalize_4 acc1 r == repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0)
let poly_update_multi_lemma_load4 text acc0 r = admit()
