module Lib.UpdateMulti.Lemmas

/// This module establishes some equivalence between the update-multi style used
/// for specifications in the streaming functor, and the lib-based repeat
/// imperative combinators.

/// This is the reason why repeat_l is hoisted
let repeat_l_input #a (block_length:pos { block_length < pow2 32 })
  (update_last: (a -> s:S.seq uint8 { S.length s < block_length } -> a))
  (input1 input2:S.seq uint8)
  (l: Lib.IntTypes.size_nat { l < block_length })
  (s: Lib.Sequence.lseq uint8 l)
  (acc: a): Lemma
    (requires S.length input1 % block_length == S.length input2 % block_length)
    (ensures repeat_l block_length update_last input1 l s acc ==
      repeat_l block_length update_last input2 l s acc)
  [ SMTPat (repeat_l block_length update_last input1 l s acc);
    SMTPat (repeat_l block_length update_last input2 l s acc) ]
=
  ()

#set-options "--fuel 0 --ifuel 0 --z3rlimit 150"
let rec update_full_is_repeat_blocks #a block_length update update_last acc input input' =
  // Lib.UpdateMulti side
  let n_blocks = S.length input / block_length in
  let blocks, rest = S.split input (n_blocks * block_length) in

  // Lib.Sequence side
  let repeat_f = repeat_f block_length update in
  let repeat_l = repeat_l block_length update_last input' in
  let repeat_acc =
    Lib.LoopCombinators.repeati n_blocks (Lib.Sequence.repeat_blocks_f block_length input repeat_f n_blocks) acc
  in
  let last = Seq.slice input (n_blocks * block_length) (S.length input) in
  let repeat_final_acc = repeat_l (S.length input % block_length) last repeat_acc in
  Lib.Sequence.lemma_repeat_blocks #uint8 block_length input repeat_f repeat_l acc;
  assert (repeat_final_acc == Lib.Sequence.repeat_blocks #uint8 block_length input repeat_f repeat_l acc);

  // General, useful facts.
  Math.Lemmas.euclidean_division_definition (S.length input) block_length;
  S.lemma_eq_intro last rest;
  assert (S.length rest == S.length input % block_length);
  Math.Lemmas.multiple_modulo_lemma n_blocks block_length;
  assert (S.length blocks % block_length = 0);

  if S.length input < block_length then begin
    Lib.UpdateMulti.update_multi_zero block_length update acc;
    Math.Lemmas.small_mod (S.length input) block_length;
    S.lemma_eq_intro input rest;
    assert (update_full block_length update update_last acc input == update_last acc input);
    Lib.LoopCombinators.eq_repeati0 n_blocks (Lib.Sequence.repeat_blocks_f block_length input repeat_f n_blocks) acc;
    assert (repeat_acc == acc);
    assert (repeat_final_acc == update_last acc input);
    assert (repeat_final_acc == update_full block_length update update_last acc input)
  end else begin
    let head, tail = Lib.UpdateMulti.split_block block_length blocks 1 in
    assert (S.length head % block_length = 0);

    S.lemma_eq_intro (head `S.append` tail `S.append` rest) input;
    S.lemma_eq_intro (head `S.append` (tail `S.append` rest)) input;
    S.lemma_eq_intro (S.slice input 0 block_length) head;
    S.lemma_eq_intro (S.slice input block_length (S.length input)) (tail `S.append` rest);
    S.lemma_len_append head (tail `S.append` rest);
    S.lemma_len_append tail rest;
    calc (==) {
      S.length (tail `S.append` rest) / block_length;
    (==) { }
      (S.length input - S.length head) / block_length;
    (==) { }
      (S.length input + (- 1) * block_length) / block_length;
    (==) { Math.Lemmas.division_addition_lemma (S.length input) block_length (-1) }
      n_blocks - 1;
    };
    // After a detailed investigation with quake, the two calls below seem to be
    // flaky. Probably worth doing a detailed proof of these two in case this
    // proof breaks in the future.
    S.lemma_eq_intro (fst (S.split (tail `S.append` rest) ((n_blocks - 1) * block_length))) tail;
    S.lemma_eq_intro (snd (S.split (tail `S.append` rest) ((n_blocks - 1) * block_length))) rest;
    assert (S.length (tail `S.append` rest) % block_length == S.length input % block_length);

    norm_spec [zeta; iota; primops; delta_only [`%mk_update_multi]]
      (mk_update_multi block_length update acc (head `S.append` tail));
    calc (==) {
      Lib.UpdateMulti.update_full block_length update update_last acc input;
    (==) { }
      update_last (mk_update_multi block_length update (update acc head) tail) rest;
    (==) { }
      Lib.UpdateMulti.update_full block_length update update_last (update acc head) (tail `S.append` rest);
    (==) { update_full_is_repeat_blocks #a block_length update update_last (update acc head) (tail `S.append` rest) input' }
      Lib.Sequence.repeat_blocks #uint8 block_length (tail `S.append` rest) repeat_f repeat_l (update acc head);
    (==) { }
      Lib.Sequence.repeat_blocks #uint8 block_length (tail `S.append` rest) repeat_f repeat_l (repeat_f head acc);
    (==) {
      Lib.LoopCombinators.eq_repeati0 1 (Lib.Sequence.repeat_blocks_f block_length head repeat_f 1) acc;
      Lib.LoopCombinators.unfold_repeati 1 (Lib.Sequence.repeat_blocks_f block_length head repeat_f 1) acc 0
    }
      Lib.Sequence.repeat_blocks #uint8 block_length (tail `S.append` rest) repeat_f repeat_l
        (Lib.LoopCombinators.repeati 1 (Lib.Sequence.repeat_blocks_f block_length head repeat_f 1) acc);

    (==) { Lib.Sequence.lemma_repeat_blocks_multi block_length head repeat_f acc }
      Lib.Sequence.repeat_blocks #uint8 block_length (tail `S.append` rest) repeat_f repeat_l
        (Lib.Sequence.repeat_blocks_multi block_length head repeat_f acc);

    (==) { Lib.Sequence.Lemmas.repeat_blocks_split block_length block_length input repeat_f repeat_l acc }
      Lib.Sequence.repeat_blocks #uint8 block_length input repeat_f repeat_l acc;
    }
  end

let repeat_blocks_extensionality #a #b bs inp f1 f2 l1 l2 init =
  // Naming things
  let len = length inp in
  let nb = len / bs in
  let rem = len % bs in
  let acc1 = Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f1 nb) init in
  let acc2 = Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f2 nb) init in
  let last = Seq.slice inp (nb * bs) len in
  let acc1' = l1 rem last acc1 in
  let acc2' = l2 rem last acc2 in
  Lib.Sequence.lemma_repeat_blocks bs inp f1 l1 init;
  Lib.Sequence.lemma_repeat_blocks bs inp f2 l2 init;
  Lib.Sequence.Lemmas.repeati_extensionality nb (repeat_blocks_f bs inp f1 nb)
    (repeat_blocks_f bs inp f2 nb) init
