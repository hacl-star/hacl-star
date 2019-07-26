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
  Lemma (
    let len = length inp in
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
  Lemma (
    let len = length inp in
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


val unfold_w:
    #a:Type0
  -> w:lanes
  -> n:pos
  -> f:(i:nat{i < w * n} -> a -> a)
  -> acc0:a ->
  Lemma (Loops.repeati (w*n) f acc0 == repeat_w w n f (n-1) (Loops.repeati (w*(n-1)) f acc0))


val normalizen_repeati_extensionality:
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
