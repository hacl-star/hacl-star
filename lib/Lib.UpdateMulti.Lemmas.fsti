module Lib.UpdateMulti.Lemmas

module S = FStar.Seq

open Lib.UpdateMulti
open FStar.Mul

let uint8 = Lib.IntTypes.uint8

#set-options "--fuel 0 --ifuel 0"

/// This module establishes some equivalence between the update-multi style used
/// for specifications in the streaming functor, and the lib-based repeat
/// imperative combinators.


/// The following lemmas characterize the result of ``split_at_last_lazy`` with
/// conditions which are easy to assess, and is very useful when using it in order 
/// to implement a stream hash, to prove properties about how to update the internal
/// buffer so that its content is actually the correct remainder of the data seen
/// so far.

/// This first auxiliary lemma only manipulates the lengths of the sequences.
val split_at_last_lazy_nb_rem_spec (l : pos) (d n rest: nat) :
  Lemma
  (requires (
    rest <= l /\
    (rest = 0 ==> d = 0) /\
    d = n * l + rest))
  (ensures ((n, rest) = split_at_last_lazy_nb_rem l d))

/// This second lemma characterizes the sequences themselves.
val split_at_last_lazy_spec (l : pos)
                            (b blocks rest: S.seq uint8) :
  Lemma
  (requires (
    S.length blocks % l = 0 /\
    S.length rest <= l /\
    (S.length rest = 0 ==> S.length b = 0) /\
    b `Seq.equal` Seq.append blocks rest))
  (ensures (
     (blocks, rest) == split_at_last_lazy l b))

/// Some helpers to flip the order of arguments
let repeat_f #a (block_length:pos { block_length < pow2 32 })
  (update: (a -> s:S.seq uint8 { S.length s = block_length } -> a))
  (b: S.seq uint8 { S.length b = block_length }) (acc: a): a
=
  update acc b

let repeat_l #a (block_length:pos { block_length < pow2 32 })
  (update_last: (a -> s:S.seq uint8 { S.length s < block_length } -> a))
  (input:S.seq uint8)
  (l: Lib.IntTypes.size_nat { l < block_length })
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
