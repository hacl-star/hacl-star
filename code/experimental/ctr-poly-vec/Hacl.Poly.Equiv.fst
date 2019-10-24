module Hacl.Poly.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Poly

module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 2"

val lemma_repeat_right_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:lanes
  -> n:nat
  -> normalize_n:(a_vec -> a)
  -> f:(i:nat{i < n * w} -> a -> a)
  -> f_vec:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc_v0:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_v:a_vec).
   (assert (w * (i + 1) <= w * n);
    normalize_n (f_vec i acc_v) == Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a a) f (normalize_n acc_v))))
  (ensures
    normalize_n (Loops.repeat_right 0 n (Loops.fixed_a a_vec) f_vec acc_v0) ==
    Loops.repeat_right 0 (w * n) (Loops.fixed_a a) f (normalize_n acc_v0))

let rec lemma_repeat_right_vec #a #a_vec w n normalize_n f f_vec acc_v0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n (Loops.fixed_a a_vec) f_vec acc_v0;
    Loops.eq_repeat_right 0 (w * n) (Loops.fixed_a a) f (normalize_n acc_v0);
    () end
  else begin
    lemma_repeat_right_vec #a #a_vec w (n - 1) normalize_n f f_vec acc_v0;
    let next_p : a_vec = Loops.repeat_right 0 (n - 1) (Loops.fixed_a a_vec) f_vec acc_v0 in
    let next_v = Loops.repeat_right 0 (w * (n - 1)) (Loops.fixed_a a) f (normalize_n acc_v0) in
    assert (normalize_n next_p == next_v);
    let res1 = Loops.repeat_right 0 n (Loops.fixed_a a_vec) f_vec acc_v0 in
    let res2 = Loops.repeat_right 0 (w * n) (Loops.fixed_a a) f (normalize_n acc_v0) in
    Loops.unfold_repeat_right 0 n (Loops.fixed_a a_vec) f_vec acc_v0 (n - 1);
    assert (res1 == f_vec (n - 1) next_p);
    Loops.repeat_right_plus 0 (w * (n - 1)) (w * n) (Loops.fixed_a a) f (normalize_n acc_v0);
    assert (res2 == Loops.repeat_right (w * (n - 1)) (w * n) (Loops.fixed_a a) f next_v);
    assert (normalize_n res1 == Loops.repeat_right (w * (n - 1)) (w * n) (Loops.fixed_a a) f next_v)
    end


//TODO: change the definition of the repeat_blocks function in Lib.Sequence
val repeat_blocks_split:
     #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks blocksize inp f l acc0 ==
    repeat_blocks blocksize (Seq.slice inp len0 len) f l
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))

let repeat_blocks_split #a #b #c blocksize len0 inp f l acc0 = admit()



#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Hacl.Poly.Equiv +Lib.Sequence +FStar.Seq +Math.Lemmas +Lib.Inttypes +Hacl.Poly'"


val repeat_blocks_last:
    #w:lanes
  -> text:bytes{length text < w * blocksize}
  -> acc_v:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   repeat_blocks #uint8 #(felem_v w) #felem (w * blocksize) text (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v ==
   poly_update_last_v #w r (length text) text acc_v)

let repeat_blocks_last #w text acc_v r =
  let pre = create w (pow_w w r) in
  let len = length text in
  let blocksize_v = w * blocksize in
  let nb = len / blocksize_v in
  Math.Lemmas.small_div len blocksize_v;
  assert (nb = 0);
  let rem = len % blocksize_v in
  let acc = Loops.repeati nb (repeat_blocks_f (w * blocksize) text (poly_update_nblocks #w pre) nb) acc_v in
  Loops.eq_repeati0 nb (repeat_blocks_f (w * blocksize) text (poly_update_nblocks #w pre) nb) acc_v;
  assert (acc == acc_v);
  let last = Seq.slice text (nb * blocksize_v) len in
  Seq.Properties.slice_length text


val repeat_blocks_multi_v_equiv_aux:
    #w:lanes
  -> text:bytes{length text % (w * blocksize) = 0}
  -> r:felem
  -> i:nat{i < length text / (w * blocksize)}
  -> acc_v:felem_v w -> Lemma
  (let len = length text in
   let blocksize_v = w * blocksize in
   let nb_vec = len / (w * blocksize) in
   let nb = len / blocksize in
   assume (nb == w * nb_vec);

   let pre = create w (pow_w w r) in
   let repeat_bf_vec = repeat_blocks_f (w * blocksize) text (poly_update_nblocks #w pre) nb_vec in
   let repeat_bf_s = repeat_blocks_f blocksize text (poly_update1 r) nb in
   assert (w * (i + 1) <= w * nb_vec);
   normalize_v r (repeat_bf_vec i acc_v) ==
   Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a felem) repeat_bf_s (normalize_v r acc_v))

let repeat_blocks_multi_v_equiv_aux #w text r i acc_v = admit()
  // let len = length text in
  // let blocksize_v = w * blocksize in
  // let nb_vec = len / blocksize_v in
  // let nb = len / blocksize in
  // assume (nb == w * nb_vec);

  // let pre = create w (pow_w w r) in
  // let f_vec = poly_update_nblocks #w pre in
  // let f = poly_update1 r in

  // let repeat_bf_vec = repeat_blocks_f blocksize_v text f_vec nb_vec in
  // let repeat_bf_s = repeat_blocks_s #w text r i in

  // assert ((i + 1) * blocksize_v <= nb_vec * blocksize_v);
  // let block = Seq.slice text (i * blocksize_v) (i * blocksize_v + blocksize_v) in
  // assert (repeat_bf_vec i acc_v == f_vec block acc_v);

  // FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  // lemma_repeat_blocks_multi blocksize block f (normalize_v r acc_v);

  // let acc0 = normalize_v r acc_v in
  // poly_update_nblocks_lemma #w r block acc_v;


val repeat_blocks_multi_v_equiv:
    #w:lanes
  -> text:bytes{length text % (w * blocksize) = 0}
  -> acc_v0:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   Math.Lemmas.mod_mult_exact (length text) blocksize w;
   normalize_v r (repeat_blocks_multi (w * blocksize) text (poly_update_nblocks #w pre) acc_v0) ==
   repeat_blocks_multi blocksize text (poly_update1 r) (normalize_v r acc_v0))

let repeat_blocks_multi_v_equiv #w text acc_v0 r =
  let len = length text in
  let nb_vec = len / (w * blocksize) in
  let nb = len / blocksize in
  assume (nb == w * nb_vec);

  let pre = create w (pow_w w r) in
  let f_vec = poly_update_nblocks #w pre in
  let f = poly_update1 r in

  let repeat_bf_vec = repeat_blocks_f (w * blocksize) text f_vec nb_vec in
  let repeat_bf_s = repeat_blocks_f blocksize text f nb in

  calc (==) {
    normalize_v r (repeat_blocks_multi (w * blocksize) text f_vec acc_v0);
    (==) { lemma_repeat_blocks_multi (w * blocksize) text f_vec acc_v0 }
    normalize_v r (Loops.repeati nb_vec repeat_bf_vec acc_v0);
    (==) { Loops.repeati_def nb_vec repeat_bf_vec acc_v0 }
    normalize_v #w r (Loops.repeat_right 0 nb_vec (Loops.fixed_a (felem_v w)) repeat_bf_vec acc_v0);
    (==) { Classical.forall_intro_2 (repeat_blocks_multi_v_equiv_aux #w text r);
      lemma_repeat_right_vec w nb_vec (normalize_v r) repeat_bf_s repeat_bf_vec acc_v0 }
    Loops.repeat_right 0 (w * nb_vec) (Loops.fixed_a felem) repeat_bf_s (normalize_v r acc_v0);
    (==) { Loops.repeati_def (w * nb_vec) repeat_bf_s (normalize_v r acc_v0) }
    Loops.repeati (w * nb_vec) repeat_bf_s (normalize_v r acc_v0);
    (==) { lemma_repeat_blocks_multi blocksize text f (normalize_v r acc_v0) }
    repeat_blocks_multi blocksize text f (normalize_v r acc_v0);
  }


val repeat_blocks_v_equiv:
    #w:lanes
  -> text:bytes
  -> acc_v0:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   repeat_blocks #uint8 #(felem_v w) #felem (w * blocksize) text (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v0 ==
   repeat_blocks #uint8 #felem #felem blocksize text (poly_update1 r) (poly_update_last r) (normalize_v r acc_v0))

let repeat_blocks_v_equiv #w text acc_v0 r =
  let blocksize_v = w * blocksize in
  let len = length text in
  let len0 = len / blocksize_v * blocksize_v in
  FStar.Math.Lemmas.cancel_mul_mod (len / blocksize_v) blocksize_v;
  assert (len0 % blocksize_v = 0);

  let pre = create w (pow_w w r) in
  let acc = repeat_blocks #uint8 #(felem_v w) #felem blocksize_v text (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v0 in
  repeat_blocks_split #uint8 #(felem_v w) #felem blocksize_v len0 text (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v0;
  let acc_v1 = repeat_blocks_multi blocksize_v (Seq.slice text 0 len0) (poly_update_nblocks #w pre) acc_v0 in
  repeat_blocks_last #w (Seq.slice text len0 len) acc_v1 r;
  assert (acc == poly_update_last_v #w r (len - len0) (Seq.slice text len0 len) acc_v1);
  assert (acc == poly_update (Seq.slice text len0 len) (normalize_v r acc_v1) r);
  assert (acc == repeat_blocks #uint8 #felem blocksize (Seq.slice text len0 len) (poly_update1 r) (poly_update_last r) (normalize_v r acc_v1));
  repeat_blocks_multi_v_equiv #w (Seq.slice text 0 len0) acc_v0 r;

  Math.Lemmas.paren_mul_right (len / blocksize_v) w blocksize;
  Math.Lemmas.cancel_mul_mod (len / blocksize_v * w) blocksize;
  assert (len0 % blocksize = 0);
  repeat_blocks_split #uint8 #felem blocksize len0 text (poly_update1 r) (poly_update_last r) (normalize_v r acc_v0)


let poly_equivalence #w text acc0 r =
  let len = length text in
  let blocksize_v = w * blocksize in
  let text0 = Seq.slice text 0 blocksize_v in
  let acc_v = load_acc_v #w text0 acc0 in
  load_acc_v_lemma #w text0 acc0 r;
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  assert (normalize_v r acc_v == repeat_blocks_multi blocksize text0 (poly_update1 r) acc0);

  let pre = create w (pow_w w r) in
  let text1 = Seq.slice text blocksize_v len in
  let res_v = repeat_blocks blocksize_v text1 (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v in
  repeat_blocks_v_equiv #w text1 acc_v r;
  assert (res_v == repeat_blocks #uint8 #felem #felem blocksize text1 (poly_update1 r) (poly_update_last r) (normalize_v r acc_v));
  repeat_blocks_split #uint8 #felem #felem blocksize blocksize_v text (poly_update1 r) (poly_update_last r) acc0
