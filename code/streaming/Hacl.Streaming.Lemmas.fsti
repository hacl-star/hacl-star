module Hacl.Streaming.Lemmas

module S = FStar.Seq

open Spec.UpdateMulti
open FStar.Mul

let uint8 = Lib.IntTypes.uint8

#set-options "--fuel 0 --ifuel 0"
let update_full #a
  (block_length:pos)
  (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a)
  (update_last: a -> (s:S.seq uint8 { S.length s < block_length }) -> a)
  (acc: a)
  (input: S.seq uint8)
=
  let n_blocks = S.length input / block_length in
  let blocks, rest = S.split input (n_blocks * block_length) in
  assert (S.length rest = S.length input % block_length);
  Math.Lemmas.multiple_modulo_lemma n_blocks block_length;
  assert (S.length blocks % block_length = 0);
  assert (S.length rest < block_length);
  update_last (mk_update_multi block_length update acc blocks) rest

/// Some helpers to flip the order of arguments
let repeat_f #a (block_length:pos { block_length < pow2 32 })
  (update: (a -> s:S.seq uint8 { S.length s = block_length } -> a))
  (input: S.seq uint8 { S.length input = block_length }) (acc: a): a
=
  update acc input

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
val update_multi_is_repeat_blocks:
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
      update_full block_length update update_last acc input))
    (decreases (S.length input))
