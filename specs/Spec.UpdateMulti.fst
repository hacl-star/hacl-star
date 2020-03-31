module Spec.UpdateMulti

/// This module defines a generic update_multi combinator, used in various
/// places, including hashes and the streaming functor. See
/// Hacl.Streaming.Lemmas for an equivalence between update_multi and the
/// Lib-style repeat combinators.

module S = FStar.Seq

open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let uint8 = Lib.IntTypes.uint8

let concat_blocks_modulo (block_len: pos) (s1 s2: S.seq uint8): Lemma
  (requires
    S.length s1 % block_len = 0 /\
    S.length s2 % block_len = 0)
  (ensures
    S.length (S.append s1 s2) % block_len = 0)
=
  let input = S.append s1 s2 in
  let input1 = s1 in
  let input2 = s2 in
  calc (==) {
    S.length input % block_len;
  (==) { S.lemma_len_append input1 input2 }
    (S.length input1 + S.length input2) % block_len;
  (==) {
    FStar.Math.Lemmas.modulo_distributivity (S.length input1) (S.length input2) (block_len)
  }
    (S.length input1 % block_len + S.length input2 % block_len) % block_len;
  (==) { (* hyp *) }
    0 % block_len;
  (==) { }
    0;
  }

/// A helper that deals with the modulo proof obligation to make things go
/// smoothly. Stolen from Spec.Agile.Hash, to be shared! Note: this version has
/// a much more robust proof.
let split_block (block_length: pos)
  (blocks: S.seq uint8)
  (n: nat):
  Pure (S.seq uint8 & S.seq uint8)
    (requires
      S.length blocks % block_length = 0 /\
      n <= S.length blocks / block_length)
    (ensures fun (l, r) ->
      S.length l % block_length = 0 /\
      S.length r % block_length = 0 /\
      l == fst (Seq.split blocks (FStar.Mul.(n * block_length))) /\
      r == snd (Seq.split blocks (FStar.Mul.(n * block_length))) /\
      S.append l r == blocks)
=
  let block, rem = S.split blocks FStar.Mul.(n * block_length) in
  Math.Lemmas.modulo_distributivity (S.length rem) (S.length block) block_length;
  Math.Lemmas.multiple_modulo_lemma (S.length blocks / block_length) block_length ;
  Math.Lemmas.multiple_modulo_lemma n block_length;
  Math.Lemmas.modulo_distributivity ((S.length blocks / block_length) * block_length) (- (S.length block)) block_length;
  S.lemma_eq_intro (block `S.append` rem) blocks;
  block, rem

let update_t a block_length =
  a -> b:S.seq uint8 { S.length b = block_length } -> a

let rec mk_update_multi #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (blocks: S.seq uint8): Pure a
  (requires
    S.length blocks % block_length = 0)
  (ensures fun _ ->
    True)
  (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    acc
  else
    let block, rem = split_block block_length blocks 1 in
    let acc = update acc block in
    mk_update_multi block_length update acc rem

#push-options "--max_fuel 1"
let update_multi_zero #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a):
  Lemma
    (ensures (mk_update_multi block_length update acc S.empty == acc))
=
  ()
#pop-options

#push-options "--fuel 1 --z3rlimit 50"
let rec update_multi_associative #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (input1 input2: S.seq uint8):
  Lemma
    (requires
      S.length input1 % block_length == 0 /\
      S.length input2 % block_length == 0)
    (ensures (
      let input = S.append input1 input2 in
      S.length input % block_length == 0 /\
      mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2 ==
        mk_update_multi block_length update acc input))
    (decreases (
      S.length input1 + S.length input2))
=
  let input = S.append input1 input2 in
  concat_blocks_modulo block_length input1 input2;
  if S.length input1 = 0 then
    calc (==) {
      mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2;
    (==) { update_multi_zero block_length update acc }
      mk_update_multi block_length update acc input2;
    (==) { S.lemma_eq_intro input2 (S.empty `S.append` input2) }
      mk_update_multi block_length update acc (S.empty `S.append` input2);
    (==) { S.lemma_eq_intro input1 S.empty }
      mk_update_multi block_length update acc (input1 `S.append` input2);
    }
  else
    let input1_hd, input1_tl = split_block block_length input1 1 in
    S.lemma_eq_intro input1 (input1_hd `S.append` input1_tl);
    update_multi_associative block_length update (update acc input1_hd) input1_tl input2;
    let s = input1_hd `S.append` (input1_tl `S.append` input2) in
    S.lemma_eq_intro (fst (S.split s (1 * block_length))) input1_hd;
    S.lemma_eq_intro (snd (S.split s (1 * block_length))) (input1_tl `S.append` input2);
    S.lemma_eq_intro (input1_hd `S.append` (input1_tl `S.append` input2)) input

#pop-options
