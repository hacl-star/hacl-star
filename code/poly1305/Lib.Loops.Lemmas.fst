module Lib.Loops.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


let rec repeati_extensionality #a n f g acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f acc0;
    Loops.eq_repeati0 n g acc0 end
  else begin
    Loops.unfold_repeati n f acc0 (n-1);
    Loops.unfold_repeati n g acc0 (n-1);
    repeati_extensionality #a (n-1) f g acc0 end


let rec repeati_right_extensionality #a n lo_g hi_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n (Loops.fixed_a a) f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n (Loops.fixed_a a) f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 (lo_g+n-1);
    repeati_right_extensionality #a (n-1) lo_g hi_g f g acc0 end


val repeat_blocks_split1:
    #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

    Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 ==
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a b) repeat_bf_t acc0)

let repeat_blocks_split1 #a #b size_block len0 inp f acc0 =
  let len = length inp in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;

  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let aux_repeat_bf (i:nat{i < len0 / size_block}) (acc:b) : Lemma
    (repeat_bf_s0 i acc == repeat_bf_t i acc)
    = let nb = len0 / size_block in
      assert ((i+1)*size_block <= nb*size_block);
      let block = Seq.slice inp (i*size_block) (i*size_block+size_block) in
      FStar.Seq.lemma_len_slice inp (i*size_block) (i*size_block+size_block);
      assert (repeat_bf_s0 i acc == f block acc);
      assert (repeat_bf_t i acc == f block acc)
  in

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_extensionality (len0 / size_block) repeat_bf_s0 repeat_bf_t acc0;
  assert (Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 == Loops.repeati (len0 / size_block) repeat_bf_t acc0);
  Loops.repeati_def (len0 / size_block) repeat_bf_t acc0

val lemma_aux: size_block:size_pos -> len:nat -> len0:nat{len0 <= len /\ len0 % size_block == 0} ->
  Lemma (len0 / size_block + (len - len0) / size_block == len / size_block)
let lemma_aux sb len len0 =
  assert (len0 == len0 / sb * sb);
  assert ((len - len0) / sb == (len - len0 / sb * sb) / sb);
  FStar.Math.Lemmas.lemma_div_plus len (- len0 / sb) sb;
  assert ((len - len0) / sb == len / sb - len0 / sb)


val repeat_blocks_split2:
    #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> acc1:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    FStar.Math.Lemmas.lemma_div_le len1 len size_block;
    let t1 = Seq.slice inp len0 len in
    let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc1)

let repeat_blocks_split2 #a #b size_block len0 inp f acc1 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;
  let t1 = Seq.slice inp len0 len in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  lemma_aux size_block len len0;
  assert (i_start + nb = len / size_block);

  let aux_repeat_bf (i:nat{i < nb}) (acc:b) : Lemma
    (repeat_bf_s1 i acc == repeat_bf_t (i_start + i) acc)
    =
      assert (i_start*size_block+(i+1)*size_block <= i_start*size_block+nb*size_block);
      let block = Seq.slice inp (i_start*size_block+i*size_block) (i_start*size_block+i*size_block+size_block) in
      assert (repeat_bf_s1 i acc == f block acc);
      assert (repeat_bf_t (i_start+i) acc == f block acc)
  in

  let acc2 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1;

  FStar.Classical.forall_intro_2 (aux_repeat_bf);
  repeati_right_extensionality nb i_start (nb+i_start) repeat_bf_s1 repeat_bf_t acc1;
  assert (
    Loops.repeat_right 0 nb (Loops.fixed_a b) repeat_bf_s1 acc1 ==
    Loops.repeat_right i_start (i_start+nb) (Loops.fixed_a b) repeat_bf_t acc1);

  assert (
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
    Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc1)


val repeat_blocks_split12:
    #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    FStar.Math.Lemmas.lemma_div_le len1 len size_block;
    let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
    let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice inp len0 len) f (len1 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

    let acc1 = Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeati (len / size_block) repeat_bf_t acc0)

let repeat_blocks_split12 #a #b size_block len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;

  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice inp len0 len) f (len1 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let acc1 = Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 in
  repeat_blocks_split1 size_block len0 inp f acc0;
  assert (acc1 == Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a b) repeat_bf_t acc0);

  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  repeat_blocks_split2 size_block len0 inp f acc1;
  assert (acc3 == Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc1);

  Loops.repeat_right_plus 0 (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc0;
  assert (acc3 == Loops.repeat_right 0 (len / size_block) (Loops.fixed_a b) repeat_bf_t acc0);
  Loops.repeati_def (len / size_block) repeat_bf_t acc0


let repeat_blocks_split #a #b size_block len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t  = repeat_blocks_f size_block inp f (len / size_block) in

  let acc1 = repeat_blocks_multi size_block t0 f acc0 in
  lemma_repeat_blocks_multi size_block t0 f acc0;

  assert (len0 == len0 / size_block * size_block);
  FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block);
  assert (len % size_block == len1 % size_block);
  let acc2 = repeat_blocks size_block t1 f l acc1 in
  lemma_repeat_blocks size_block t1 f l acc1;

  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  let last = Seq.slice t1 (len1 / size_block * size_block) len1 in
  let acc4 = l (len1 % size_block) last acc3 in
  assert (acc2 == acc4);

  assert (acc1 == Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);

  repeat_blocks_split12 size_block len0 inp f acc0;
  assert (acc3 == Loops.repeati (len / size_block) repeat_bf_t acc0);

  assert (last == Seq.slice (Seq.slice inp len0 len) (len1 / size_block * size_block) len1);
  FStar.Seq.Properties.slice_slice inp len0 len (len1 / size_block * size_block) len1;
  assert (last == Seq.slice inp (len / size_block * size_block) len);

  lemma_repeat_blocks size_block inp f l acc0
