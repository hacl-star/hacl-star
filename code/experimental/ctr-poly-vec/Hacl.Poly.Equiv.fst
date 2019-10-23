module Hacl.Poly.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Poly

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

module Loops = Lib.LoopCombinators

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


val repeat_blocks_multi_v_equiv:
    #w:lanes
  -> text:bytes{length text % (w * blocksize) = 0}
  -> acc_v0:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   Math.Lemmas.mod_mult_exact (length text) blocksize w;
   normalize_v r (repeat_blocks_multi (w * blocksize) text (poly_update_nblocks #w pre) acc_v0) ==
   repeat_blocks_multi blocksize text (poly_update1 r) (normalize_v r acc_v0))

let repeat_blocks_multi_v_equiv #w text acc_v0 r = admit()




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
