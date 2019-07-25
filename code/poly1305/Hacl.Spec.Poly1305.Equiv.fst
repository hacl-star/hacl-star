module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module PLoops = Lib.Loops.Lemmas
module S = Spec.Poly1305
module Lemmas = Hacl.Spec.Poly1305.Equiv.Lemmas

include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -Hacl.Spec.*'"

val poly_update_repeat_blocks_multi_lemma:
    #w:lanes
  -> text:bytes{length text % (w * size_block) = 0}
  -> acc:elem w
  -> r:pfelem ->
  Lemma
    (normalize_n #w (repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (poly1305_update_nblocks #w (compute_rw #w r)) acc) r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) (normalize_n #w acc r))

let poly_update_repeat_blocks_multi_lemma #w text acc r =
  match w with
  | 1 -> Lemmas.poly_update_repeat_blocks_multi_lemma1 text acc r
  | 2 -> Lemmas.poly_update_repeat_blocks_multi_lemma2 text acc r
  | 4 -> Lemmas.poly_update_repeat_blocks_multi_lemma4 text acc r


val poly_update_multi_lemma_load:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (w * size_block) in
    normalize_n #w (load_acc #w acc0 t0) r ==
      repeat_blocks_multi #uint8 #pfelem size_block t0 (S.poly1305_update1 r size_block) acc0)

let poly_update_multi_lemma_load #w text acc0 r =
  match w with
  | 1 -> Lemmas.poly_update_multi_lemma_load1 text acc0 r
  | 2 -> Lemmas.poly_update_multi_lemma_load2 text acc0 r
  | 4 -> Lemmas.poly_update_multi_lemma_load4 text acc0 r


val poly_update_multi_lemma:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
    Lemma
    (poly1305_update_multi #w text acc0 r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) acc0)

let poly_update_multi_lemma #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in

  let t0 = Seq.slice text 0 len0 in
  let t1 = Seq.slice text len0 len in

  let f = S.poly1305_update1 r size_block in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let acc1 = load_acc #w acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (poly1305_update_nblocks #w rw) acc1 in
  let acc3 = normalize_n #w acc2 r in
  assert (acc3 == poly1305_update_multi #w text acc0 r);
  poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block t1 f (normalize_n acc1 r));

  poly_update_multi_lemma_load #w text acc0 r;
  assert (normalize_n acc1 r == repeat_blocks_multi #uint8 #pfelem size_block t0 f acc0);
  PLoops.repeat_blocks_multi_split #uint8 #pfelem size_block len0 text f acc0


val poly_eq_lemma:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma (poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)

let poly_eq_lemma #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  FStar.Math.Lemmas.cancel_mul_mod (len / sz_block) sz_block;
  assert (len0 % sz_block = 0);
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  let f = S.poly1305_update1 r size_block in
  let l = S.poly1305_update_last r in

  if len0 > 0 then begin
    poly_update_multi_lemma #w t0 acc0 r;
    PLoops.repeat_blocks_split #uint8 #pfelem size_block len0 text f l acc0 end
  else ()


val poly1305_vec_is_poly1305:
    #w:lanes
  -> msg:bytes
  -> k:S.key ->
  Lemma (poly1305_mac #w msg k == S.poly1305_mac msg k)

let poly1305_vec_is_poly1305 #w msg k =
  let acc0, r = S.poly1305_init k in
  poly_eq_lemma #w msg acc0 r
