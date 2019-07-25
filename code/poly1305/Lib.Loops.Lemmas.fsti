module Lib.Loops.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

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
