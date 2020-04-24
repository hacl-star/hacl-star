module Hacl.Streaming.Lemmas

module S = FStar.Seq

open Lib.UpdateMulti
open FStar.Mul

let uint8 = Lib.IntTypes.uint8

#set-options "--fuel 0 --ifuel 0"

/// Some helpers to flip the order of arguments
let repeat_f #a (block_length:pos { block_length < pow2 32 })
  (update: (a -> s:S.seq uint8 { S.length s = block_length } -> a))
  (b: S.seq uint8 { S.length b = block_length }) (acc: a): a
=
  update acc b

let repeat_l #a (block_length:pos { block_length < pow2 32 })
  (update_last: (a -> s:S.seq uint8 { S.length s < block_length } -> a))
  (input:S.seq uint8)
  (l: Lib.IntTypes.size_nat { l == S.length input % block_length })
  (s: Lib.Sequence.lseq uint8 l)
  (acc: a): a
=
  update_last acc s

#set-options "--max_fuel 0 --max_ifuel 0"
/// Note that I am using a trick here to avoid reasoning about functional
/// extensionality equality for the repeat_l helper... in a sense, I am proving
/// as I go that repeat_l only depends on ``length input % block_length``, not
/// on the nature of input itself. Clients will of course instantiate this lemma
/// with input and input' being the same.
val update_full_is_repeat_blocks:
  #a:Type0 ->
  block_length:pos { block_length < pow2 32 } ->
  update: (a -> s:S.seq uint8 { S.length s = block_length } -> a) ->
  update_last: (a -> s:S.seq uint8 { S.length s < block_length } -> a) ->
  acc:a ->
  input:S.seq uint8 ->
  input':S.seq uint8 ->
  Lemma
    (requires (
      S.length input % block_length == S.length input' % block_length))
    (ensures (
      let repeat_f = repeat_f block_length update in
      let repeat_l = repeat_l block_length update_last input' in

      Lib.Sequence.repeat_blocks #uint8 block_length input repeat_f repeat_l acc ==
      Lib.UpdateMulti.update_full block_length update update_last acc input))
    (decreases (S.length input))

open Lib.IntTypes
open Lib.Sequence

val repeat_blocks_extensionality:
  #a:Type0 ->
  #b:Type0 ->
  bs:size_pos ->
  inp:seq a ->
  f1:(lseq a bs -> b -> b) ->
  f2:(lseq a bs -> b -> b) ->
  l1:(len:size_nat{len == length inp % bs} -> s:lseq a len -> b -> b) ->
  l2:(len:size_nat{len == length inp % bs} -> s:lseq a len -> b -> b) ->
  init:b ->
  Lemma
    (requires (
      let nb = length inp / bs in (
      // condition for f1/f2
      forall (i:nat{i < nb}) (acc: b). {:pattern repeat_blocks_f bs inp f1 nb i acc}
      repeat_blocks_f bs inp f1 nb i acc == repeat_blocks_f bs inp f2 nb i acc) /\ (
      // condition for l1/l2
      let rem = length inp % bs in
      let last = Seq.slice inp (nb * bs) (length inp) in
      forall (acc: b). {:pattern l1 rem last acc }
      l1 rem last acc == l2 rem last acc)
    ))
    (ensures
      repeat_blocks bs inp f1 l1 init == repeat_blocks bs inp f2 l2 init)
