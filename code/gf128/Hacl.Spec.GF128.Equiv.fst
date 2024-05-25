module Hacl.Spec.GF128.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

open Spec.GaloisField
open Hacl.Spec.GF128.Lemmas

module Loops = Lib.LoopCombinators
module PLoops = Lib.Sequence.Lemmas
module S = Spec.GF128

include Hacl.Spec.GF128.Vec
include Lib.Vec.Lemmas


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val gf128_update_multi_add_mul_lemma_loop:
    r:elem
  -> text:bytes{length text % 64 = 0}
  -> acc0:elem
  -> i:nat{i < length text / 64}
  -> acc:elem ->
  Lemma
  (let pre = load_precompute_r r in
   let len = length text in

   let f = S.gf128_update1 r in
   let f_vec = gf128_update4_add_mul pre in
   let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
   let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

   repeat_bf_vec i acc == Loops.repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc)

let gf128_update_multi_add_mul_lemma_loop r text acc0 i acc =
  let pre = load_precompute_r r in
  let len = length text in

  let f = S.gf128_update1 r in
  let f_vec = gf128_update4_add_mul pre in
  let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
  let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

  let acc1 = repeat_bf_vec i acc in
  let b0 = S.encode (Seq.slice text (i * 64) (i * 64 + 16)) in
  let b1 = S.encode (Seq.slice text (i * 64 + 16) (i * 64 + 32)) in
  let b2 = S.encode (Seq.slice text (i * 64 + 32) (i * 64 + 48)) in
  let b3 = S.encode (Seq.slice text (i * 64 + 48) (i * 64 + 64)) in

  let acc_vec1 = load_acc (Seq.slice text (i * 64) (i * 64 + 64)) acc in
  assert (acc1 == (acc +% b0) *% pre.[0] +% (zero +% b1) *% pre.[1] +% (zero +% b2) *% pre.[2] +% (zero +% b3) *% pre.[3]);

  let acc2 = Loops.repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc in
  Loops.unfold_repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc (4 * i + 3);
  Loops.unfold_repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc (4 * i + 2);
  Loops.unfold_repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc (4 * i + 1);
  Loops.unfold_repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc (4 * i);
  Loops.eq_repeat_right (4 * i) (4 * i + 4) (Loops.fixed_a elem) repeat_bf_sc acc;

  assert (acc2 == ((((acc +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r);
  gf128_update_multi_mul_add_lemma_load_acc_aux acc b0 b1 b2 b3 pre.[3];
  assert (acc2 == acc1)


val gf128_update_multi_add_mul_lemma: text:bytes{length text % 64 = 0} -> acc0:elem -> r:elem -> Lemma
  (let pre = load_precompute_r r in
   repeat_blocks_multi #uint8 #elem 64 text (gf128_update4_add_mul pre) acc0 ==
   repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_add_mul_lemma text acc0 r =
  let len = length text in
  let pre = load_precompute_r r in

  let f = S.gf128_update1 r in
  let f_vec = gf128_update4_add_mul pre in
  let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
  let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

  let acc1 = repeat_blocks_multi #uint8 #elem 64 text f_vec acc0 in
  lemma_repeat_blocks_multi #uint8 #elem 64 text f_vec acc0;
  assert (acc1 == Loops.repeati (len / 64) repeat_bf_vec acc0);

  FStar.Classical.forall_intro_2 (gf128_update_multi_add_mul_lemma_loop r text acc0);
  Lib.Vec.Lemmas.lemma_repeati_vec 4 (len / 64) (fun x -> x) repeat_bf_sc repeat_bf_vec acc0;
  assert (acc1 == Loops.repeati (len / 16) repeat_bf_sc acc0);
  lemma_repeat_blocks_multi #uint8 #elem 16 text f acc0

val gf128_update_multi_lemma:
    text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
  Lemma
  (gf128_update_multi text acc0 r ==
   repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_lemma text acc0 r =
  gf128_update_multi_add_mul_lemma text acc0 r

val gf128_update_vec_eq_lemma:
    text:bytes
  -> acc0:elem
  -> r:elem ->
  Lemma (gf128_update_vec text acc0 r == S.gf128_update text acc0 r)

let gf128_update_vec_eq_lemma text acc0 r =
  let len = length text in
  let len0 = len / 64 * 64 in

  assert (len0 % 64 = 0);
  assert (len0 % 16 = 0);
  let t0 = Seq.slice text 0 len0 in
  let f = S.gf128_update1 r in
  let l = S.gf128_update_last r in

  if len0 > 0 then begin
    gf128_update_multi_lemma t0 acc0 r;
    PLoops.repeat_blocks_split #uint8 #elem 16 len0 text f l acc0 end
  else ()
