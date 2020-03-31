module Hacl.Streaming.Lemmas

/// This module establishes some equivalence between the update-multi style used
/// for specifications in the streaming functor, and the lib-based repeat
/// imperative combinators.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let rec update_multi_is_repeat_blocks #a block_length update update_last acc input =
  // Spec.UpdateMulti side
  let n_blocks = S.length input / block_length in
  let blocks, rest = S.split input (n_blocks * block_length) in

  // Lib.Sequence side
  let repeat_f = fun (input: S.seq uint8 { S.length input = block_length }) (acc: a) -> update acc input in
  let repeat_l = fun (l: Lib.IntTypes.size_nat { l == S.length input % block_length })
    (s: Lib.Sequence.lseq uint8 l) (acc: a) ->
    update_last acc s
  in
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
    Spec.UpdateMulti.update_multi_zero block_length update acc;
    Math.Lemmas.small_mod (S.length input) block_length;
    S.lemma_eq_intro input rest;
    assert (update_full block_length update update_last acc input == update_last acc input);
    Lib.LoopCombinators.eq_repeati0 n_blocks (Lib.Sequence.repeat_blocks_f block_length input repeat_f n_blocks) acc;
    assert (repeat_acc == acc);
    assert (repeat_final_acc == update_last acc input);
    assert (repeat_final_acc == update_full block_length update update_last acc input)
  end else begin
    let head, tail = Spec.UpdateMulti.split_block block_length blocks 1 in
    S.lemma_eq_intro (head `S.append` tail `S.append` rest) input;
    S.lemma_eq_intro (head `S.append` (tail `S.append` rest)) input;
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
    S.lemma_eq_intro (fst (S.split (tail `S.append` rest) ((n_blocks - 1) * block_length))) tail;
    S.lemma_eq_intro (snd (S.split (tail `S.append` rest) ((n_blocks - 1) * block_length))) rest;

    norm_spec [zeta; iota; primops; delta_only [`%mk_update_multi]]
      (mk_update_multi block_length update acc (head `S.append` tail));
    calc (==) {
      update_full block_length update update_last acc input;
    (==) { }
      update_last (mk_update_multi block_length update (update acc head) tail) rest;
    (==) { }
      update_full block_length update update_last (update acc head) (tail `S.append` rest);
    };

    update_multi_is_repeat_blocks #a block_length update update_last (update acc head) (tail `S.append` rest);
    assert (update_full block_length update update_last (update acc head) (tail `S.append` rest) ==
      Lib.Sequence.repeat_blocks #uint8 block_length (tail `S.append` rest) repeat_f repeat_l (update acc head));

    Lib.LoopCombinators.unfold_repeati n_blocks
      (Lib.Sequence.repeat_blocks_f block_length input repeat_f n_blocks) acc (n_blocks - 1);
    admit ()
  end
