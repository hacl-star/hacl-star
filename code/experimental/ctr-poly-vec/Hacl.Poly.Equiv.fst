module Hacl.Poly.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Poly
open Hacl.Poly.Lemmas

module Loops = Lib.LoopCombinators
module PLoops = Lib.Sequence.Lemmas


#reset-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

val lemma_repeat_blocks1:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> bs:size_pos
  -> inp:seq a
  -> f:(lseq a bs -> b -> b)
  -> l:(len:size_nat{len == length inp % bs} -> s:lseq a len -> b -> c)
  -> init:b -> Lemma
   (let len = length inp in
    let nb = len / bs in
    let rem = len % bs in
    let inp0 = Seq.slice inp 0 (nb * bs) in
    Math.Lemmas.cancel_mul_mod nb bs;
    let acc = repeat_blocks_multi bs inp0 f init in
    let last = Seq.slice inp (nb * bs) len in
    let acc = l rem last acc in
    repeat_blocks #a #b bs inp f l init == acc)

let lemma_repeat_blocks1 #a #b #c bs inp f l init =
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let inp0 = Seq.slice inp 0 (nb * bs) in
  Math.Lemmas.cancel_mul_mod nb bs;
  let acc = repeat_blocks_multi bs inp0 f init in
  lemma_repeat_blocks_multi bs inp0 f init;
  Math.Lemmas.cancel_mul_div nb bs;
  assert (acc == Loops.repeati nb (repeat_blocks_f bs inp0 f nb) init);

  let last = Seq.slice inp (nb * bs) len in
  let acc_f = l rem last acc in

  let rb = repeat_blocks #a #b bs inp f l init in
  lemma_repeat_blocks #a #b bs inp f l init;
  let acc1 = Loops.repeati nb (repeat_blocks_f bs inp f nb) init in
  assert (rb == l rem last acc1);

  let aux (i:nat{i < nb}) (acc:b) : Lemma
    (repeat_blocks_f bs inp0 f nb i acc == repeat_blocks_f bs inp f nb i acc) =
    Math.Lemmas.lemma_mult_le_right bs (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * bs) (i * bs) (i * bs + bs) in

  Classical.forall_intro_2 aux;
  PLoops.repeati_extensionality nb (repeat_blocks_f bs inp f nb) (repeat_blocks_f bs inp0 f nb) init



let lanes = w:size_pos{w * blocksize <= max_size_t}

val repeat_blocks_multi_vec_equiv_pre_lemma: #w:lanes -> r:felem -> b:block_v w -> acc_v0:felem_v w -> Lemma
  (let pre = create w (pow_w w r) in
   let f = poly_update1 r in
   let f_v = poly_update_nblocks #w pre in

   PLoops.repeat_blocks_multi_vec_equiv_pre w blocksize (w * blocksize) f f_v (normalize_v r) b acc_v0)

let repeat_blocks_multi_vec_equiv_pre_lemma #w r b acc_v0 =
  poly_update_nblocks_lemma #w r b acc_v0


val poly_update_multi_lemma_v:
    #w:lanes
  -> text:bytes{length text % (w * blocksize) = 0}
  -> acc_v0:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   let f = poly_update1 r in
   let f_v = poly_update_nblocks #w pre in

   Math.Lemmas.mod_mult_exact (length text) blocksize w;
   normalize_v r (repeat_blocks_multi (w * blocksize) text f_v acc_v0) ==
   repeat_blocks_multi blocksize text f (normalize_v r acc_v0))

let poly_update_multi_lemma_v #w text acc_v0 r =
  let pre = create w (pow_w w r) in
  let f = poly_update1 r in
  let f_v = poly_update_nblocks #w pre in

  Classical.forall_intro_2 (repeat_blocks_multi_vec_equiv_pre_lemma #w r);
  Math.Lemmas.mod_mult_exact (length text) blocksize w;
  PLoops.lemma_repeat_blocks_multi_vec w blocksize text f f_v (normalize_v r) acc_v0


val poly_update_v_lemma:
    #w:lanes
  -> text:bytes{w * blocksize <= length text}
  -> acc0:felem
  -> r:felem ->
  Lemma (poly_update_v #w text acc0 r == poly_update text acc0 r)

let poly_update_v_lemma #w text acc0 r =
  let len = length text in
  let blocksize_v = w * blocksize in
  let pre = create w (pow_w w r) in

  let f = poly_update1 r in
  let g = poly_update_last r in
  let f_v = poly_update_nblocks #w pre in
  let g_v = poly_update_last_v #w r in

  let text0 = Seq.slice text 0 blocksize_v in
  let acc_v = load_acc_v #w text0 acc0 in

  let text1 = Seq.slice text blocksize_v len in
  let acc_v1 = repeat_blocks #uint8 #(felem_v w) #felem blocksize_v text1 f_v g_v acc_v in
  lemma_repeat_blocks1 #uint8 #(felem_v w) #felem blocksize_v text1 f_v g_v acc_v;

  let len1 = length text1 in
  let nb1 = len1 / blocksize_v in
  let rem1 = len1 % blocksize_v in
  let inp0 = Seq.slice text1 0 (nb1 * blocksize_v) in
  Math.Lemmas.cancel_mul_mod nb1 blocksize_v;
  let acc = repeat_blocks_multi blocksize_v inp0 f_v acc_v in
  poly_update_multi_lemma_v #w inp0 acc_v r;
  Math.Lemmas.mod_mult_exact (length inp0) blocksize w;
  assert (
    normalize_v r (repeat_blocks_multi blocksize_v inp0 f_v acc_v) ==
    repeat_blocks_multi blocksize inp0 f (normalize_v r acc_v));
  let last = Seq.slice text1 (nb1 * blocksize_v) len1 in
  let acc = g_v rem1 last acc in
  assert (acc_v1 == acc);
  PLoops.repeat_blocks_split blocksize (nb1 * blocksize_v) text1 f g (normalize_v r acc_v);
  assert (acc_v1 == poly_update text1 (normalize_v r acc_v) r);
  load_acc_v_lemma #w text0 acc0 r;
  Math.Lemmas.cancel_mul_mod w blocksize;
  assert (blocksize_v % blocksize = 0);
  assert (normalize_v r acc_v == repeat_blocks_multi blocksize text0 f acc0);
  PLoops.repeat_blocks_split blocksize blocksize_v text f g acc0;
  assert (acc_v1 == poly_update text acc0 r)


let poly_equivalence #w text acc r =
  poly_update_v_lemma #w text acc r
