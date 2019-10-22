module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module PLoops = Lib.Sequence.Lemmas
module Lemmas = Hacl.Spec.Poly1305.Lemmas
module S = Spec.Poly1305

include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val poly_update_multi_lemma_load_acc1:
    r:pfelem
  -> text:bytes{size_block <= length text /\ length text % size_block = 0}
  -> acc0:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 size_block in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f 1 in
    normalize_n r (load_acc1 t0 acc0) == PLoops.repeat_w #pfelem 1 1 repeat_bf_t0 0 acc0)

let poly_update_multi_lemma_load_acc1 r text acc0 = ()


val poly_update_multi_lemma_load_acc2:
    r:pfelem
  -> text:bytes{2 * size_block <= length text /\ length text % (2 * size_block) = 0 /\ length text % size_block = 0}
  -> acc0:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (2 * size_block) in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f 2 in
    normalize_n r (load_acc2 t0 acc0) == PLoops.repeat_w #pfelem 2 1 repeat_bf_t0 0 acc0)

let poly_update_multi_lemma_load_acc2 r text acc0 =
  let t0 = Seq.slice text 0 (2 * size_block) in
  let f = S.poly1305_update1 r size_block in
  let repeat_bf_t0 = repeat_blocks_f size_block t0 f 2 in
  assert (PLoops.repeat_w #pfelem 2 1 repeat_bf_t0 0 acc0 == repeat_bf_t0 1 (repeat_bf_t0 0 acc0));

  let b0 = Seq.slice text 0 size_block in
  let b1 = Seq.slice text size_block (2 * size_block) in

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  assert (repeat_bf_t0 1 (repeat_bf_t0 0 acc0) == pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r);

  let acc1 = load_acc2 t0 acc0 in
  let acc2 = normalize_n r acc1 in
  assert (acc2 == pfadd (pfmul acc1.[0] (pfmul r r)) (pfmul acc1.[1] r));
  assert (acc1.[0] == pfadd acc0 c0);
  assert (acc1.[1] == pfadd 0 c1);
  FStar.Math.Lemmas.modulo_lemma c1 prime;
  assert (acc1.[1] == c1);
  assert (acc2 == pfadd (pfmul (pfadd acc0 c0) (pfmul r r)) (pfmul c1 r));
  Lemmas.poly_update_multi_lemma_load2_simplify acc0 r c0 c1


val poly_update_multi_lemma_load_acc4:
    r:pfelem
  -> text:bytes{4 * size_block <= length text /\ length text % (4 * size_block) = 0 /\ length text % size_block = 0}
  -> acc0:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (4 * size_block) in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f 4 in
    normalize_n r (load_acc4 t0 acc0) == PLoops.repeat_w #pfelem 4 1 repeat_bf_t0 0 acc0)

let poly_update_multi_lemma_load_acc4 r text acc0 =
  let t0 = Seq.slice text 0 (4 * size_block) in
  let f = S.poly1305_update1 r size_block in
  let repeat_bf_t0 = repeat_blocks_f size_block t0 f 4 in

  let acc1 = PLoops.repeat_w #pfelem 4 1 repeat_bf_t0 0 acc0 in
  assert (acc1 == repeat_bf_t0 3 (repeat_bf_t0 2 (repeat_bf_t0 1 (repeat_bf_t0 0 acc0))));

  let b0 = Seq.slice text 0 size_block in
  let b1 = Seq.slice text size_block (2 * size_block) in
  let b2 = Seq.slice text (2 * size_block) (3 * size_block) in
  let b3 = Seq.slice text (3 * size_block) (4 * size_block) in

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
  let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in
  assert (acc1 == pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r) c2) r) c3) r);

  let acc2 = load_acc4 t0 acc0 in
  let acc3 = normalize_4 r acc2 in
  assert (acc2.[0] == pfadd acc0 c0);
  FStar.Math.Lemmas.modulo_lemma c1 prime;
  FStar.Math.Lemmas.modulo_lemma c2 prime;
  FStar.Math.Lemmas.modulo_lemma c3 prime;
  assert (acc2.[1] == c1);
  assert (acc2.[2] == c2);
  assert (acc2.[3] == c3);
  assert (acc3 ==
    pfadd (pfadd (pfadd (pfmul (pfadd acc0 c0) (pfmul (pfmul r r) (pfmul r r)))
      (pfmul c1 (pfmul (pfmul r r) r))) (pfmul c2 (pfmul r r))) (pfmul c3 r));
  Lemmas.poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3;
  assert (acc1 == acc3)


val poly_update_multi_lemma_load_acc:
    #w:lanes
  -> r:pfelem
  -> text:bytes{w * size_block <= length text /\ length text % (w * size_block) = 0 /\ length text % size_block = 0}
  -> acc0:pfelem ->
  Lemma
   (let t0 = Seq.slice text 0 (w * size_block) in
    let f = S.poly1305_update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
    normalize_n r (load_acc #w t0 acc0) == PLoops.repeat_w #pfelem w 1 repeat_bf_t0 0 acc0)

let poly_update_multi_lemma_load_acc #w r text acc0 =
  match w with
  | 1 -> poly_update_multi_lemma_load_acc1 r text acc0
  | 2 -> poly_update_multi_lemma_load_acc2 r text acc0
  | 4 -> poly_update_multi_lemma_load_acc4 r text acc0


val poly_update_multi_lemma_loop1:
    r:pfelem
  -> text:bytes{size_block <= length text /\ length text % size_block = 0}
  -> i:nat{i < (length text - size_block) / size_block}
  -> acc_vec:elem 1 ->
  Lemma
   (let rw = compute_rw #1 r in
    let len = length text in
    let len1 = len - size_block in

    let nb_vec = len1 / size_block in
    let nb = len1 / size_block in
    assert (nb == nb_vec);

    let t1 = Seq.slice text size_block len in
    let f = S.poly1305_update1 r size_block in
    let f_vec = Vec.poly1305_update_nblocks rw in
    let repeat_bf_vec = repeat_blocks_f size_block t1 f_vec nb_vec in
    let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in
    normalize_n r (repeat_bf_vec i acc_vec) == PLoops.repeat_w #pfelem 1 nb_vec repeat_bf_t1 i (normalize_n r acc_vec))

let poly_update_multi_lemma_loop1 r text i acc_vec = ()


val poly_update_multi_lemma_loop2:
    r:pfelem
  -> text:bytes{2 * size_block <= length text /\ length text % (2 * size_block) = 0 /\ length text % size_block = 0}
  -> i:nat{i < (length text - 2 * size_block) / (2 * size_block)}
  -> acc_vec:elem 2 ->
  Lemma
   (let rw = compute_rw #2 r in
    let len = length text in
    let len1 = len - 2 * size_block in

    let nb_vec = len1 / (2 * size_block) in
    let nb = len1 / size_block in
    assert (nb == 2 * nb_vec);

    let t1 = Seq.slice text (2 * size_block) len in
    let f = S.poly1305_update1 r size_block in
    let f_vec = Vec.poly1305_update_nblocks rw in
    let repeat_bf_vec = repeat_blocks_f (2 * size_block) t1 f_vec nb_vec in
    let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in
    normalize_n r (repeat_bf_vec i acc_vec) == PLoops.repeat_w #pfelem 2 nb_vec repeat_bf_t1 i (normalize_n r acc_vec))

let poly_update_multi_lemma_loop2 r text i acc_vec0 =
  let rw = compute_rw #2 r in
  let len = length text in
  let len1 = len - 2 * size_block in

  let nb_vec = len1 / (2 * size_block) in
  let nb = len1 / size_block in
  assert (nb == 2 * nb_vec);

  let t1 = Seq.slice text (2 * size_block) len in
  let f = S.poly1305_update1 r size_block in
  let f_vec = Vec.poly1305_update_nblocks rw in
  let repeat_bf_vec = repeat_blocks_f (2 * size_block) t1 f_vec nb_vec in
  let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in

  let acc1 = PLoops.repeat_w #pfelem 2 nb_vec repeat_bf_t1 i (normalize_n r acc_vec0) in
  assert (acc1 == repeat_bf_t1 (2*i+1) (repeat_bf_t1 (2*i) (normalize_2 r acc_vec0)));

  let b0 = Seq.slice t1 (i * 32) (i * 32 + 16) in
  let b1 = Seq.slice t1 (i * 32 + 16) (i * 32 + 32) in
  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in

  let acc_vec1 = repeat_bf_vec i acc_vec0 in
  Lemmas.poly_update_repeat_blocks_multi_lemma2_simplify acc_vec0.[0] acc_vec0.[1] c0 c1 r;
  assert (normalize_2 r acc_vec1 == PLoops.repeat_w #pfelem 2 nb_vec repeat_bf_t1 i (normalize_n r acc_vec0))


#set-options "--z3rlimit 150"

val poly_update_multi_lemma_loop4:
    r:pfelem
  -> text:bytes{4 * size_block <= length text /\ length text % (4 * size_block) = 0 /\ length text % size_block = 0}
  -> i:nat{i < (length text - 4 * size_block) / (4 * size_block)}
  -> acc_vec:elem 4 ->
  Lemma
   (let rw = compute_rw #4 r in
    let len = length text in
    let len1 = len - 4 * size_block in

    let nb_vec = len1 / (4 * size_block) in
    let nb = len1 / size_block in
    assert (nb == 4 * nb_vec);

    let t1 = Seq.slice text (4 * size_block) len in
    let f = S.poly1305_update1 r size_block in
    let f_vec = Vec.poly1305_update_nblocks rw in
    let repeat_bf_vec = repeat_blocks_f (4 * size_block) t1 f_vec nb_vec in
    let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in
    normalize_n r (repeat_bf_vec i acc_vec) == PLoops.repeat_w #pfelem 4 nb_vec repeat_bf_t1 i (normalize_n r acc_vec))

let poly_update_multi_lemma_loop4 r text i acc_vec0 =
  let rw = compute_rw #4 r in
  let len = length text in
  let len1 = len - 4 * size_block in

  let nb_vec = len1 / (4 * size_block) in
  let nb = len1 / size_block in
  assert (nb == 4 * nb_vec);

  let t1 = Seq.slice text (4 * size_block) len in
  let f = S.poly1305_update1 r size_block in
  let f_vec = Vec.poly1305_update_nblocks rw in
  let repeat_bf_vec = repeat_blocks_f (4 * size_block) t1 f_vec nb_vec in
  let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in

  let acc1 = PLoops.repeat_w #pfelem 4 nb_vec repeat_bf_t1 i (normalize_n r acc_vec0) in
  assert (acc1 == repeat_bf_t1 (4*i+3) (repeat_bf_t1 (4*i+2)
    (repeat_bf_t1 (4*i+1) (repeat_bf_t1 (4*i) (normalize_4 r acc_vec0)))));

  let b0 = Seq.slice t1 (i * 64) (i * 64 + 16) in
  let b1 = Seq.slice t1 (i * 64 + 16) (i * 64 + 32) in
  let b2 = Seq.slice t1 (i * 64 + 32) (i * 64 + 48) in
  let b3 = Seq.slice t1 (i * 64 + 48) (i * 64 + 64) in
  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
  let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in
  let r2 = pfmul r r in
  let r4 = pfmul r2 r2 in

  let acc_vec1 = repeat_bf_vec i acc_vec0 in
  Lemmas.poly_update_repeat_blocks_multi_lemma4_simplify
    acc_vec0.[0] acc_vec0.[1] acc_vec0.[2] acc_vec0.[3] c0 c1 c2 c3 r r2 r4;
  assert (normalize_n r acc_vec1 == PLoops.repeat_w #pfelem 4 nb_vec repeat_bf_t1 i (normalize_n r acc_vec0))


val poly_update_multi_lemma_loop:
    #w:lanes
  -> r:pfelem
  -> text:bytes{w * size_block <= length text /\ length text % (w * size_block) = 0 /\ length text % size_block = 0}
  -> i:nat{i < (length text - w * size_block) / (w * size_block)}
  -> acc_vec:elem w ->
  Lemma
   (let rw = compute_rw #w r in
    let len = length text in
    let len1 = len - w * size_block in

    let nb_vec = len1 / (w * size_block) in
    let nb = len1 / size_block in
    assert (nb == w * nb_vec);

    let t1 = Seq.slice text (w * size_block) len in
    let f = S.poly1305_update1 r size_block in
    let f_vec = Vec.poly1305_update_nblocks rw in
    let repeat_bf_vec = repeat_blocks_f (w * size_block) t1 f_vec nb_vec in
    let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in
    normalize_n r (repeat_bf_vec i acc_vec) == PLoops.repeat_w #pfelem w nb_vec repeat_bf_t1 i (normalize_n r acc_vec))

let poly_update_multi_lemma_loop #w r text i acc_vec =
  match w with
  | 1 -> poly_update_multi_lemma_loop1 r text i acc_vec
  | 2 -> poly_update_multi_lemma_loop2 r text i acc_vec
  | 4 -> poly_update_multi_lemma_loop4 r text i acc_vec


val poly_update_multi_lemma:
    #w:lanes
  -> text:bytes{w * size_block <= length text /\ length text % (w * size_block) = 0 /\ length text % size_block = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (poly1305_update_multi #w text acc0 r ==
    repeat_blocks_multi #uint8 #pfelem size_block text (S.poly1305_update1 r size_block) acc0)

let poly_update_multi_lemma #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
  assert (len % len0 == len1 % len0);

  let t0 = Seq.slice text 0 len0 in
  let t1 = Seq.slice text len0 len in

  let acc1 = load_acc #w t0 acc0 in
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (poly1305_update_nblocks #w rw) acc1 in
  let acc3 = normalize_n #w r acc2 in
  assert (acc3 == poly1305_update_multi #w text acc0 r);

  let nb_vec = len1 / (w * size_block) in
  let nb = len1 / size_block in
  assert (nb == w * nb_vec);

  let f = S.poly1305_update1 r size_block in
  let f_vec = Vec.poly1305_update_nblocks rw in

  let repeat_bf_vec = repeat_blocks_f (w * size_block) t1 f_vec nb_vec in
  let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
  let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in

  poly_update_multi_lemma_load_acc #w r text acc0;
  //assert (normalize_n r (load_acc #w t0 acc0) == PLoops.repeat_w #pfelem w 1 repeat_bf_t0 0 acc0);
  FStar.Classical.forall_intro_2 (poly_update_multi_lemma_loop #w r text);
  //assert (forall (i:nat{i < nb_vec}) (acc_vec:elem w).
    //  normalize_n r (repeat_bf_vec i acc_vec) == PLoops.repeat_w #pfelem w nb_vec repeat_bf_t1 i (normalize_n r acc_vec));

  PLoops.lemma_repeat_blocks_multi_vec #uint8 #pfelem #(elem w)
    w size_block text f f_vec (normalize_n r) (load_acc #w) acc0


val poly1305_update_vec_lemma:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma (poly1305_update #w text acc0 r == S.poly1305_update text acc0 r)

let poly1305_update_vec_lemma #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  FStar.Math.Lemmas.cancel_mul_mod (len / sz_block) sz_block;
  assert (len0 % sz_block = 0);
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  let f = S.poly1305_update1 r size_block in
  let l = S.poly1305_update_last r in

  if len0 > 0 then
    begin
    poly_update_multi_lemma #w t0 acc0 r;
    PLoops.repeat_blocks_split #uint8 #pfelem size_block len0 text f l acc0
    end


val poly1305_vec_lemma:
    #w:lanes
  -> msg:bytes
  -> k:S.key ->
  Lemma (poly1305_mac #w msg k == S.poly1305_mac msg k)

let poly1305_vec_lemma #w msg k =
  let acc0, r = S.poly1305_init k in
  poly1305_update_vec_lemma #w msg acc0 r
