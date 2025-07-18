module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module VecLemmas = Lib.Vec.Lemmas
module S = Spec.Poly1305

include Hacl.Spec.Poly1305.Vec

let block_v (w:lanes{w * size_block <= max_size_t}) = lbytes (w * size_block)

///
///  val load_acc_lemma: #w:lanes -> b:block_v w -> acc0:pfelem -> r:pfelem -> Lemma
///   (normalize_n r (load_acc b acc0) == repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) acc0)
///

val load_acc_lemma1: b:block_v 1 -> acc0:pfelem -> r:pfelem -> Lemma
  (normalize_n r (load_acc #1 b acc0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) acc0)


val load_acc_lemma2: b:block_v 2 -> acc0:pfelem -> r:pfelem -> Lemma
  (normalize_n r (load_acc b acc0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) acc0)

val load_acc_lemma4: b:block_v 4 -> acc0:pfelem -> r:pfelem -> Lemma
  (normalize_n r (load_acc b acc0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) acc0)

val load_acc_lemma: #w:lanes -> b:block_v w -> acc0:pfelem -> r:pfelem -> Lemma
  (normalize_n r (load_acc b acc0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) acc0)

///
///  val poly_update_nblocks_lemma: #w:lanes -> r:pfelem -> b:block_v w -> acc_v0:elem w -> Lemma
///  (let rw = compute_rw r in
///   normalize_n r (poly_update_nblocks #w rw b acc_v0) ==
///   repeat_blocks_multi size_block b (poly_update1 r) (normalize_n r acc_v0))
///

val poly_update_nblocks_lemma1: r:pfelem -> b:block_v 1 -> acc_v0:elem 1 -> Lemma
  (let rw = compute_rw #1 r in
   normalize_n r (poly1305_update_nblocks rw b acc_v0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) (normalize_n r acc_v0))

#push-options "--z3smtopt '(set-option :smt.arith.solver 2)'"
// ^ needed to check the statements!
val poly_update_nblocks_lemma2: r:pfelem -> b:block_v 2 -> acc_v0:elem 2 -> Lemma
  (let rw = compute_rw #2 r in
   normalize_n r (poly1305_update_nblocks rw b acc_v0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) (normalize_n r acc_v0))

val poly_update_nblocks_lemma4: r:pfelem -> b:block_v 4 -> acc_v0:elem 4 -> Lemma
  (let rw = compute_rw #4 r in
   normalize_n r (poly1305_update_nblocks rw b acc_v0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) (normalize_n r acc_v0))
#pop-options

val poly_update_nblocks_lemma: #w:lanes -> r:pfelem -> b:block_v w -> acc_v0:elem w -> Lemma
  (let rw = compute_rw #w r in
   normalize_n r (poly1305_update_nblocks rw b acc_v0) ==
   repeat_blocks_multi size_block b (S.poly1305_update1 r size_block) (normalize_n r acc_v0))

val repeat_blocks_multi_vec_equiv_pre_lemma: #w:lanes -> r:pfelem -> b:block_v w -> acc_v0:elem w -> Lemma
  (let rw = compute_rw #w r in
   let f = S.poly1305_update1 r size_block in
   let f_v = poly1305_update_nblocks rw in
   VecLemmas.repeat_blocks_multi_vec_equiv_pre w size_block f f_v (normalize_n r) b acc_v0)

val poly_update_multi_lemma_v:
    #w:lanes
  -> text:bytes{length text % (w * size_block) = 0 /\ length text % size_block = 0}
  -> acc_v0:elem w
  -> r:pfelem -> Lemma
  (let rw = compute_rw #w r in
   let f = S.poly1305_update1 r size_block in
   let f_v = poly1305_update_nblocks rw in
   normalize_n r (repeat_blocks_multi (w * size_block) text f_v acc_v0) ==
   repeat_blocks_multi size_block text f (normalize_n r acc_v0))

val poly_update_multi_lemma:
    #w:lanes
  -> text:bytes{w * size_block <= length text /\ length text % (w * size_block) = 0 /\ length text % size_block = 0}
  -> acc0:pfelem
  -> r:pfelem -> Lemma
  (poly1305_update_multi #w text acc0 r ==
   repeat_blocks_multi size_block text (S.poly1305_update1 r size_block) acc0)

val poly1305_update_vec_lemma: #w:lanes -> text:bytes -> acc0:pfelem -> r:pfelem ->
  Lemma (poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)

val poly1305_vec_lemma: #w:lanes -> msg:bytes -> k:S.key ->
  Lemma (poly1305_mac #w msg k == S.poly1305_mac msg k)
