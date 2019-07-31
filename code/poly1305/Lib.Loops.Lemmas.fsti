module Lib.Loops.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  (Loops.repeati n f acc0 == Loops.repeati n g acc0))


val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures (Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0))


val repeat_blocks_split:
     #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> l:(len:size_nat{len == length inp % size_block} -> s:lseq a len -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block);
    assert (len % size_block == (len - len0) % size_block);
    repeat_blocks size_block inp f l acc0 ==
    repeat_blocks size_block (Seq.slice inp len0 len) f l
      (repeat_blocks_multi size_block (Seq.slice inp 0 len0) f acc0))


val repeat_blocks_multi_split:
     #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp /\ length inp % size_block = 0}
  -> f:(lseq a size_block -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block);
    assert (len % size_block == (len - len0) % size_block);
    repeat_blocks_multi size_block inp f acc0 ==
    repeat_blocks_multi size_block (Seq.slice inp len0 len) f
      (repeat_blocks_multi size_block (Seq.slice inp 0 len0) f acc0))


let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}

let repeat_w (#a:Type0) (w:lanes) (n:nat) (f:(i:nat{i < w * n} -> a -> a)) (i:nat{i < n}) (acc:a) : Tot a =
  match w with
  | 1 -> f i acc
  | 2 -> f (2*i+1) (f (2*i) acc)
  | 4 -> f (4*i+3) (f (4*i+2) (f (4*i+1) (f (4*i) acc)))


val unfold_repeatw:
    #a:Type0
  -> w:lanes
  -> n:pos
  -> f:(i:nat{i < w * n} -> a -> a)
  -> acc0:a ->
  Lemma (Loops.repeati (w*n) f acc0 == repeat_w w n f (n-1) (Loops.repeati (w*(n-1)) f acc0))


val lemma_repeati_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:lanes
  -> n:nat
  -> normalize_n:(a_vec -> a)
  -> f:(i:nat{i < n * w} -> a -> a)
  -> f_vec:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc0_vec:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_vec:a_vec). normalize_n (f_vec i acc_vec) == repeat_w w n f i (normalize_n acc_vec)))
  (ensures  (normalize_n (Loops.repeati n f_vec acc0_vec) == Loops.repeati (w * n) f (normalize_n acc0_vec)))


private
val lemma_aux1: w:pos -> size_block:pos -> len:pos ->
  Lemma
  (requires (w * size_block <= len /\ len % (w * size_block) = 0 /\ len % size_block = 0))
  (ensures  ((len - w * size_block) / size_block == w * ((len - w * size_block) / (w * size_block))))


val lemma_repeat_blocks_multi_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a{w * size_block <= length inp /\ length inp % (w * size_block) = 0 /\ length inp % size_block = 0}
  -> f:(lseq a size_block -> b -> b)
  -> f_vec:(lseq a (w * size_block) -> b_vec -> b_vec)
  -> normalize_n:(b_vec -> b)
  -> load_acc:(lseq a (w * size_block) -> b -> b_vec)
  -> acc0:b ->
  Lemma
  (requires
   (let len = length inp in
    let len0 = w * size_block in
    let len1 = len - len0 in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == len1 % len0);
    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    let nb_vec = len1 / (w * size_block) in
    let nb = len1 / size_block in
    lemma_aux1 w size_block len;
    assert (nb == w * nb_vec);
    let repeat_bf_vec = repeat_blocks_f (w * size_block) t1 f_vec nb_vec in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
    let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in

    normalize_n (load_acc t0 acc0) == repeat_w #b w 1 repeat_bf_t0 0 acc0 /\
    (forall (i:nat{i < nb_vec}) (acc_vec:b_vec).
      normalize_n (repeat_bf_vec i acc_vec) == repeat_w #b w nb_vec repeat_bf_t1 i (normalize_n acc_vec))))
  (ensures
   (let len = length inp in
    let len0 = w * size_block in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == (len - len0) % len0);

    let acc_vec = load_acc (Seq.slice inp 0 len0) acc0 in
    normalize_n (repeat_blocks_multi #a #b_vec (w * size_block) (Seq.slice inp len0 len) f_vec acc_vec) ==
    repeat_blocks_multi #a #b size_block inp f acc0))
