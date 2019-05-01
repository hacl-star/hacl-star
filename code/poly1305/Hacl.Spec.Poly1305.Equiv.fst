module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module S = Spec.Poly1305
module Lemmas = Hacl.Spec.Poly1305.Equiv.Lemmas

include Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 150 --max_fuel 2"

val poly_update_repeat_blocks_multi_lemma:
    #w:lanes
  -> text:bytes{length text % (w * size_block) = 0}
  -> acc:elem w
  -> r:pfelem ->
  Lemma
    (normalize_n #w (repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (updaten #w (compute_rw #w r)) acc) r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) (normalize_n #w acc r))
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
      repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0)
let poly_update_multi_lemma_load #w text acc0 r =
  match w with
  | 1 -> Lemmas.poly_update_multi_lemma_load1 text acc0 r
  | 2 -> Lemmas.poly_update_multi_lemma_load2 text acc0 r
  | 4 -> Lemmas.poly_update_multi_lemma_load4 text acc0 r

//
// Lemma
//   (poly_update_multi #w text acc0 r ==
//      repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) acc0)
//

#set-options "--max_fuel 1"

val poly_update_multi_lemma1:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let rw = compute_rw #w r in
    let len = length text in
    let len0 = w * size_block in
    let t0 = Seq.slice text 0 len0 in
    let f = update1 r size_block in
    let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
    normalize_n #w (load_acc #w acc0 t0) r ==
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a pfelem) repeat_bf_t0 acc0)
let poly_update_multi_lemma1 #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;

  let f = update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let acc1 = load_acc #w acc0 t0 in
  poly_update_multi_lemma_load #w text acc0 r;
  assert (normalize_n #w acc1 r == repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0);
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0;
  assert (normalize_n #w acc1 r == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);

  let aux_repeat_bf (i:nat{i < len0 / size_block}) (acc:pfelem) : Lemma
    (repeat_bf_s0 i acc == repeat_bf_t0 i acc)
    = let nb = len0 / size_block in
      assert ((i+1) * size_block <= nb * size_block);
      let block = Seq.slice text (i*size_block) (i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (i*size_block) (i*size_block+size_block);
      assert (repeat_bf_s0 i acc == f block acc);
      assert (repeat_bf_t0 i acc == f block acc)
  in

  let rec aux (n:nat{n <= len0 / size_block}) : Lemma
    (Loops.repeati n repeat_bf_s0 acc0 == Loops.repeati n repeat_bf_t0 acc0) =
    let nb = len0 / size_block in
    if n = 0 then (
      Loops.eq_repeati0 n repeat_bf_s0 acc0;
      Loops.eq_repeati0 n repeat_bf_t0 acc0
    ) else (
      Loops.unfold_repeati n repeat_bf_s0 acc0 (n-1);
      Loops.unfold_repeati n repeat_bf_t0 acc0 (n-1);
      aux (n-1);
      let next_p = Loops.repeati (n-1) repeat_bf_s0 acc0 in
      let next_v = Loops.repeati (n-1) repeat_bf_t0 acc0 in
      assert (next_p == next_v);
      aux_repeat_bf (n-1) next_p;
      assert (repeat_bf_s0 (n-1) next_p == repeat_bf_t0 (n-1) next_v)
    )
  in aux (len0 / size_block);
  assert (normalize_n #w acc1 r == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);
  Loops.repeati_def (len0 / size_block) repeat_bf_t0 acc0

val poly_update_multi_lemma2:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
   (let rw = compute_rw #w r in
    let len = length text in
    let len0 = w * size_block in
    let t0 = Seq.slice text 0 len0 in
    let t1 = Seq.slice text len0 len in
    let f = update1 r size_block in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = load_acc #w acc0 t0 in
    let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (updaten #w rw) acc1 in
    normalize_n #w acc2 r ==
      Loops.repeat_right (len0 / size_block) (len / size_block)
        (Loops.fixed_a pfelem) repeat_bf_t1 (normalize_n #w acc1 r))
let poly_update_multi_lemma2 #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let len0 = w * size_block in
  let len1 = len - len0 in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;

  let f = update1 r size_block in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

  let acc1 = load_acc #w acc0 t0 in
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (updaten #w rw) acc1 in
  let acc3 = normalize_n #w acc2 r in
  assert (acc3 == poly_update_multi #w text acc0 r);
  poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block t1 (update1 r size_block) (normalize_n #w acc1 r));
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t1 (update1 r size_block) (normalize_n #w acc1 r);
  assert (acc3 == Loops.repeati (len1 / size_block) repeat_bf_s1 (normalize_n #w acc1 r));
  let acc1_s = normalize_n #w acc1 r in

  Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1_s;
  assert (acc3 ==
    Loops.repeat_right 0 (len1 / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_s1 acc1_s);

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  assert (i_start + nb = len / size_block);

  let aux_repeat_bf (i:nat{i < nb}) (acc:pfelem) : Lemma
    (repeat_bf_s1 i acc == repeat_bf_t1 (i_start + i) acc)
    =
      let start = i_start * size_block in
      assert (start + (i+1) * size_block <= start + nb * size_block);
      let block = Seq.slice text (start+i*size_block) (start+i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (start+i*size_block) (start+i*size_block+size_block);
      assert (repeat_bf_s1 i acc == f block acc);
      assert (repeat_bf_t1 (len0 / size_block + i) acc == f block acc)
  in

  let rec aux (n:nat{n <= nb}) : Lemma
    (Loops.repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s ==
     Loops.repeat_right i_start (i_start+n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1_s) =
    if n = 0 then (
      Loops.eq_repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s;
      Loops.eq_repeat_right i_start (i_start+n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1_s
    ) else (
      Loops.unfold_repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s (n-1);
      Loops.unfold_repeat_right i_start (i_start+n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1_s (i_start+n-1);
      aux (n-1);
      let next_p = Loops.repeat_right 0 (n-1) (Loops.fixed_a pfelem) repeat_bf_s1 acc1_s in
      let next_v = Loops.repeat_right i_start (i_start+n-1) (Loops.fixed_a pfelem) repeat_bf_t1 acc1_s in
      assert (i_start+n-1 == i_start+(n-1));
      assert (next_p == next_v);
      aux_repeat_bf (n-1) next_p;
      assert (repeat_bf_s1 (n-1) next_p == repeat_bf_t1 (i_start+n-1) next_v)
    )
  in aux nb;
  assert (acc3 ==
    Loops.repeat_right (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc1_s)

val poly_update_multi_lemma:
    #w:lanes
  -> text:bytes{0 < length text /\ length text % (w * size_block) = 0}
  -> acc0:pfelem
  -> r:pfelem ->
    Lemma
    (poly_update_multi #w text acc0 r ==
      repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) acc0)
let poly_update_multi_lemma #w text acc0 r =
  let rw = compute_rw #w r in
  let len = length text in
  let f = update1 r size_block in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in

  let len0 = w * size_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let acc1 = load_acc #w acc0 t0 in
  poly_update_multi_lemma1 #w text acc0 r;
  assert (normalize_n #w acc1 r ==
    Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a pfelem) repeat_bf_t0 acc0);

  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;
  let acc2 = repeat_blocks_multi #uint8 #(elem w) (w * size_block) t1 (updaten #w rw) acc1 in
  let acc3 = normalize_n #w acc2 r in
  assert (acc3 == poly_update_multi #w text acc0 r);
  poly_update_repeat_blocks_multi_lemma #w t1 acc1 r;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block t1 (update1 r size_block) (normalize_n acc1 r));
  poly_update_multi_lemma2 #w text acc0 r;
  assert (acc3 ==
   Loops.repeat_right (len0 / size_block) (len / size_block)
     (Loops.fixed_a pfelem) repeat_bf_t0 (normalize_n #w acc1 r));

  Loops.repeat_right_plus
    0 (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t0 acc0;
  assert (acc3 ==
    Loops.repeat_right 0 (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t0 acc0);
  Loops.repeati_def (len / size_block) repeat_bf_t0 acc0;
  lemma_repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) acc0;
  assert (acc3 == repeat_blocks_multi #uint8 #pfelem size_block text (update1 r size_block) acc0)

//
// Lemma
//   (poly #w text acc0 r == poly_update1 text acc0 r)
//

#push-options "--z3rlimit 200"
val poly_eq_lemma1:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let f = update1 r size_block in
    let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice text 0 len0) f (len0 / size_block) in
    let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
    Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 ==
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a pfelem) repeat_bf_t0 acc0))
let poly_eq_lemma1 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;

  let f = update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice text 0 len0) (update1 r size_block) (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text (update1 r size_block) (len / size_block) in

  let acc1 = poly_update_multi #w t0 acc0 r in
  poly_update_multi_lemma #w t0 acc0 r;
  assert (acc1 == repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0);
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0;
  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);

  let aux_repeat_bf (i:nat{i < len0 / size_block}) (acc:pfelem) : Lemma
    (repeat_bf_s0 i acc == repeat_bf_t0 i acc)
    = let nb = len0 / size_block in
      assert ((i+1) * size_block <= nb * size_block);
      let block = Seq.slice text (i*size_block) (i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (i*size_block) (i*size_block+size_block);
      assert (repeat_bf_s0 i acc == f block acc);
      assert (repeat_bf_t0 i acc == f block acc)
  in

  let rec aux (n:nat{n <= len0 / size_block}) : Lemma
    (Loops.repeati n repeat_bf_s0 acc0 == Loops.repeati n repeat_bf_t0 acc0) =
    let nb = len0 / size_block in
    if n = 0 then (
      Loops.eq_repeati0 nb repeat_bf_s0 acc0;
      Loops.eq_repeati0 nb repeat_bf_t0 acc0
    ) else (
      Loops.unfold_repeati nb repeat_bf_s0 acc0 (n-1);
      Loops.unfold_repeati nb repeat_bf_t0 acc0 (n-1);
      aux (n-1);
      let next_p = Loops.repeati (n-1) repeat_bf_s0 acc0 in
      let next_v = Loops.repeati (n-1) repeat_bf_t0 acc0 in
      assert (next_p == next_v);
      aux_repeat_bf (n-1) next_p;
      assert (repeat_bf_s0 (n-1) next_p == repeat_bf_t0 (n-1) next_v)
    )
  in aux (len0 / size_block);
  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_t0 acc0);
  Loops.repeati_def (len0 / size_block) repeat_bf_t0 acc0
#pop-options

#push-options "--z3rlimit 200"
#push-options "--max_fuel 2"
val poly_eq_lemma2:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let len1 = len - len0 in
    let f = update1 r size_block in
    let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = poly_update_multi #w (Seq.slice text 0 len0) acc0 r in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a pfelem) repeat_bf_t1 acc1))
let poly_eq_lemma2 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  FStar.Math.Lemmas.multiple_modulo_lemma len0 size_block;
  assert (len0 % size_block = 0);
  let len1 = len - len0 in
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let t1 = Seq.slice text len0 len in
  FStar.Seq.Base.lemma_len_slice text len0 len;

  let f = update1 r size_block in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

  let acc1 = poly_update_multi #w t0 acc0 r in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1;
  assert (acc3 ==
    Loops.repeat_right 0 (len1 / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_s1 acc1);

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  assert (i_start + nb = len / size_block);

  let aux_repeat_bf (i:nat{i < nb}) (acc:pfelem) : Lemma
    (repeat_bf_s1 i acc == repeat_bf_t1 (i_start + i) acc)
    =
      let start = i_start * size_block in
      assert (start + (i+1) * size_block <= start + nb * size_block);
      let block = Seq.slice text (start+i*size_block) (start+i*size_block+size_block) in
      FStar.Seq.lemma_len_slice text (start+i*size_block) (start+i*size_block+size_block);
      assert (repeat_bf_s1 i acc == f block acc);
      assert (repeat_bf_t1 (i_start + i) acc == f block acc)
  in

  let rec aux (n:nat{n <= nb}) : Lemma
    (Loops.repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1 ==
     Loops.repeat_right i_start (i_start + n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1) =
    if n = 0 then (
      Loops.eq_repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1;
      Loops.eq_repeat_right i_start (i_start+n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1
    ) else (
      let lp = Loops.repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1 in
      let rp = Loops.repeat_right i_start (i_start + n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1 in
      Loops.unfold_repeat_right 0 n (Loops.fixed_a pfelem) repeat_bf_s1 acc1 (n-1);
      Loops.unfold_repeat_right i_start (i_start+n) (Loops.fixed_a pfelem) repeat_bf_t1 acc1 (i_start+n-1);
      let next_p = Loops.repeat_right 0 (n-1) (Loops.fixed_a pfelem) repeat_bf_s1 acc1 in
      let next_v = Loops.repeat_right i_start (i_start+n-1) (Loops.fixed_a pfelem) repeat_bf_t1 acc1 in
      assert (lp == repeat_bf_s1 (n-1) next_p);
      assert (rp == repeat_bf_t1 (i_start+n-1) next_v);
      aux (n-1);
      assert (next_p == next_v);
      aux_repeat_bf (n-1) next_p;
      assert (repeat_bf_s1 (n-1) next_p == repeat_bf_t1 (i_start+n-1) next_v)
    )
  in aux nb;
  assert (
    acc3 ==
    Loops.repeat_right (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc1)
#pop-options

val poly_eq_lemma12:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures (
    let len = length text in
    let sz_block = w * size_block in
    let len0 = len / sz_block * sz_block in
    let len1 = len - len0 in
    let f = update1 r size_block in
    let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
    let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in

    let acc1 = poly_update_multi #w (Seq.slice text 0 len0) acc0 r in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeati (len / size_block) repeat_bf_t1 acc0))
let poly_eq_lemma12 #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let acc1 = poly_update_multi #w t0 acc0 r in
  poly_update_multi_lemma #w t0 acc0 r;
  lemma_repeat_blocks_multi #uint8 #pfelem size_block t0 (update1 r size_block) acc0;

  let f = update1 r size_block in
  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice text 0 len0) f (len0 / size_block) in
  let repeat_bf_t0 = repeat_blocks_f size_block text f (len / size_block) in
  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);
  poly_eq_lemma1 #w text acc0 r;
  assert (acc1 ==
    Loops.repeat_right 0 (len0 / size_block)
    (Loops.fixed_a pfelem) repeat_bf_t0 acc0);

  let t1 = Seq.slice text len0 len in
  let len1 = len - len0 in
  FStar.Seq.Base.lemma_len_slice text len0 len;
  let acc2 = poly_update1 t1 acc1 r in
  lemma_repeat_blocks #uint8 #pfelem size_block t1 f (poly_update1_rem r) acc1;

  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  poly_eq_lemma2 #w text acc0 r;
  assert (acc3 ==
    Loops.repeat_right (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc1);

  Loops.repeat_right_plus
    0 (len0 / size_block) (len / size_block)
    (Loops.fixed_a pfelem)
    (repeat_blocks_f size_block text (update1 r size_block) (len / size_block)) acc0;
  assert (acc3 ==
    Loops.repeat_right 0 (len / size_block)
    (Loops.fixed_a pfelem)
    repeat_bf_t1 acc0);
  Loops.repeati_def (len / size_block) repeat_bf_t1 acc0

val poly_eq_lemma_pos:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block > 0))
  (ensures poly #w text acc0 r == poly_update1 text acc0 r)
let poly_eq_lemma_pos #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  assert (len0 % size_block = 0);
  let t0 = Seq.slice text 0 len0 in
  FStar.Seq.Base.lemma_len_slice text 0 len0;
  let acc1 = poly_update_multi #w t0 acc0 r in

  let t1 = Seq.slice text len0 len in
  let len1 = len - len0 in
  FStar.Seq.Base.lemma_len_slice text len0 len;
  let acc2 = poly_update1 t1 acc1 r in

  let f = update1 r size_block in
  lemma_repeat_blocks #uint8 #pfelem size_block t1 f (poly_update1_rem r) acc1;

  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice text len0 len) f (len1 / size_block) in
  let repeat_bf_t1 = repeat_blocks_f size_block text f (len / size_block) in
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  let last = Seq.slice t1 (len1 / size_block * size_block) len1 in
  let acc4 = poly_update1_rem r (len1 % size_block) last acc3 in
  assert (acc2 == acc4);

  poly_eq_lemma12 #w text acc0 r;
  assert (acc3 == Loops.repeati (len / size_block) repeat_bf_t1 acc0);

  assert (last == Seq.slice (Seq.slice text len0 len) (len1 / size_block * size_block) len1);
  FStar.Seq.Properties.slice_slice text len0 len (len1 / size_block * size_block) len1;
  assert (last == Seq.slice text (len / size_block * size_block) len);

  lemma_repeat_blocks #uint8 #pfelem size_block text f (poly_update1_rem r) acc0


val poly_eq_lemma_zero:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
  (requires (
    let len = length text in
    let sz_block = w * size_block in
    len / sz_block * sz_block == 0))
  (ensures poly #w text acc0 r == poly_update1 text acc0 r)
let poly_eq_lemma_zero #w text acc0 r = ()

val poly_eq_lemma:
    #w:lanes
  -> text:bytes
  -> acc0:pfelem
  -> r:pfelem ->
  Lemma
    (poly #w text acc0 r == poly_update1 text acc0 r)
let poly_eq_lemma #w text acc0 r =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  if len0 > 0 then
    poly_eq_lemma_pos #w text acc0 r
  else
    poly_eq_lemma_zero #w text acc0 r

val update1_eq_lemma:
    r:pfelem
  -> len:size_nat{len <= size_block}
  -> b:lbytes len
  -> acc:pfelem ->
  Lemma
    (update1 r len b acc == S.update1 r len b acc)
let update1_eq_lemma r len b acc =
  let e = nat_from_bytes_le b in
  assert (e < pow2 (len * 8));
  Math.Lemmas.pow2_le_compat 128 (len * 8);
  assert_norm (pow2 128 + pow2 128 < prime);
  let e1 = pfadd (pow2 (8 * len)) e in
  FStar.Math.Lemmas.modulo_lemma (pow2 (8 * len) + e) prime

//chacha20poly1305/Hacl.Spec.Poly1305.Equiv.fst
val poly_eq_lemma_vec:
    #w:lanes
  -> text:bytes
  -> acc:pfelem
  -> r:pfelem ->
  Lemma
    (poly_update #1 text acc r == Spec.Poly1305.poly text acc r)
let poly_eq_lemma_vec #w text acc r =
  let len = length text in
  let nb = len / size_block in
  let rem = len % size_block in

  let f = S.update1 r 16 in
  let f_vec = update1 r 16 in
  let repeat_bf_s = repeat_blocks_f size_block text f nb in
  let repeat_bf_v = repeat_blocks_f size_block text f_vec nb in

  lemma_repeat_blocks #uint8 #pfelem size_block text f_vec (poly_update1_rem r) acc;
  lemma_repeat_blocks #uint8 #S.felem size_block text f (S.poly_update1_rem r) acc;

  let acc_s = Loops.repeati nb repeat_bf_s acc in
  let acc_v = Loops.repeati nb repeat_bf_v acc in

  let aux_repeat_bf (i:nat{i < nb}) (acc:pfelem) :
    Lemma (repeat_bf_s i acc == repeat_bf_v i acc)
    = assert (repeat_bf_v i acc = repeat_blocks_f size_block text f_vec nb i acc);
      assert ((i+1) * 16 <= nb * 16);
      let block = Seq.slice text (i*16) (i*16+16) in
      FStar.Seq.lemma_len_slice text (i*16) (i*16+16);
      assert (repeat_bf_s i acc == f block acc);
      assert (repeat_bf_v i acc == f_vec block acc);
      update1_eq_lemma r size_block block acc
  in

  let rec aux (n:nat{n <= nb}) : Lemma
    (Loops.repeati n repeat_bf_s acc == Loops.repeati n repeat_bf_v acc) =
    if n = 0 then (
      Loops.eq_repeati0 n repeat_bf_s acc;
      Loops.eq_repeati0 n repeat_bf_v acc
    ) else (
      let lp = Loops.repeati n repeat_bf_s acc in
      let rp = Loops.repeati n repeat_bf_v acc in
      Loops.unfold_repeati n repeat_bf_s acc (n-1);
      let next_s = Loops.repeati (n-1) repeat_bf_s acc in
      assert (lp == repeat_bf_s (n-1) next_s);
      Loops.unfold_repeati n repeat_bf_v acc (n-1);
      let next_v = Loops.repeati (n-1) repeat_bf_v acc in
      assert (rp == repeat_bf_v (n-1) next_v);
      aux (n-1);
      assert (next_s == next_v);
      aux_repeat_bf (n-1) next_v;
      assert (repeat_bf_s (n-1) next_s == repeat_bf_v (n-1) next_v)
    )
  in aux nb;

  let last = Seq.slice text (nb * size_block) len in
  FStar.Seq.lemma_len_slice text (nb * size_block) len;
  FStar.Math.Lemmas.lemma_div_mod len size_block;
  update1_eq_lemma r rem last acc_v

val lemma_repeat_blocks_exact_size:
    r:pfelem
  -> b:lbytes 16
  -> acc:pfelem ->
  Lemma (
    let f = update1 r 16 in
    let l = poly_update1_rem r in
    repeat_blocks #uint8 #pfelem size_block b f l acc ==
     l 0 Seq.empty (f b acc))
let lemma_repeat_blocks_exact_size r b acc =
  let f = update1 r 16 in
  let l = poly_update1_rem r in
  lemma_repeat_blocks 16 b f l acc;

  let acc1 = Lib.LoopCombinators.repeati 1 (repeat_blocks_f 16 b f 1) acc in
  Lib.LoopCombinators.unfold_repeati 1 (repeat_blocks_f 16 b f 1) acc 0;
  Lib.LoopCombinators.eq_repeati0 1 (repeat_blocks_f 16 b f 1) acc;
  Seq.slice_length b;
  assert (Seq.slice b 0 16 == b);
  let last = Seq.slice b 16 16 in
  Seq.slice_is_empty b 16;
  assert (last == Seq.empty)

#reset-options "--z3rlimit 50"

val lemma_repeat_blocks_small_size:
    r:pfelem
  -> len:size_nat{0 < len /\ len < 16}
  -> b:lbytes len
  -> acc:pfelem ->
  Lemma (
    let f = update1 r 16 in
    let l = poly_update1_rem r in
    repeat_blocks #uint8 #pfelem size_block b f l acc ==
     l len b acc)
let lemma_repeat_blocks_small_size r len b acc =
  let f = update1 r 16 in
  let l = poly_update1_rem r in
  lemma_repeat_blocks 16 b f l acc;

  let acc1 = Lib.LoopCombinators.repeati 0 (repeat_blocks_f 16 b f 0) acc in
  Lib.LoopCombinators.eq_repeati0 0 (repeat_blocks_f 16 b f 0) acc;
  assert (acc1 == acc);
  Seq.slice_length b;
  assert (Seq.slice b 0 len == b)

val poly_update1_is_update1:
    r:pfelem
  -> len:size_nat{0 < len /\ len <= size_block}
  -> b:lbytes len
  -> acc:pfelem
  -> Lemma
    (poly_update #1 b acc r == S.update1 r len b acc)
let poly_update1_is_update1 r len b acc =
  let f = update1 r 16 in
  let l = poly_update1_rem r in
  assert (poly_update #1 b acc r ==
    repeat_blocks #uint8 #pfelem size_block b f l acc);
  lemma_repeat_blocks 16 b f l acc;
  if len = 16 then begin
    lemma_repeat_blocks_exact_size r b acc;
    update1_eq_lemma r len b acc end
  else begin
    lemma_repeat_blocks_small_size r len b acc;
    update1_eq_lemma r len b acc end

val poly1305_vec_is_poly1305:
    #w:lanes
  -> msg:bytes
  -> k:key ->
  Lemma
    (poly1305 #w msg k ==  Spec.Poly1305.poly1305 msg k)
let poly1305_vec_is_poly1305 #w msg k =
  let acc0, r = poly1305_init k in
  poly_eq_lemma #w msg acc0 r;
  poly_eq_lemma_vec #w msg acc0 r
