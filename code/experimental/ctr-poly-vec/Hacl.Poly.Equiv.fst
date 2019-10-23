module Hacl.Poly.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Poly

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


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


val repeat_blocks_v_equiv:
    #w:lanes
  -> text:bytes
  -> acc_v0:felem_v w
  -> r:felem -> Lemma
  (let pre = create w (pow_w w r) in
   repeat_blocks #uint8 #(felem_v w) #felem (w * blocksize) text (poly_update_nblocks #w pre) (poly_update_last_v #w r) acc_v0 ==
   repeat_blocks #uint8 #felem #felem blocksize text (poly_update1 r) (poly_update_last r) (normalize_v r acc_v0))

let repeat_blocks_v_equiv #w text acc_v0 r = admit()
// call `repeat_blocks_split` with len0 = len / bs_v * bs_v [f_v; [f; g]]
// repeat_blocks_multi (v == s) [f; [f; g]]
// call `repeat_blocks_multi_split` [f; g]


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
