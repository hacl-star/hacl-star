module Lib.UpdateMulti.Lemmas

/// This first auxiliary lemma only manipulates the lengths of the sequences.
#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_lazy_nb_rem_spec (l : pos) (d n rest: nat) :
  Lemma
  (requires (
    rest <= l /\
    (rest = 0 ==> d = 0) /\
    d = n * l + rest))
  (ensures ((n, rest) = split_at_last_lazy_nb_rem l d)) =
  (* We call ``split_at_last_lazy_nb_rem`` at the beginning to have its
   * postcondition in the context (the return values are only used in the second
   * branch *)
  let n', rest' = split_at_last_lazy_nb_rem l d in 
  if d = 0 then
     begin
     Math.Lemmas.nat_times_nat_is_nat n l;
     Math.Lemmas.int_times_int_equal_zero_lemma n l;
     assert(n = 0)
     end
  else
   begin
     assert(d > 0);
     (* In order to prove the equality between all the lengths, we use the unicity
     * of the modulo to prove that the rests are equal, then that the numbers
     * of blocks are equal. *)
     let blocks = n * l in
     let rest = d - blocks in
     let blocks' = n' * l in
     Math.Lemmas.cancel_mul_mod n l;
     assert(blocks % l = 0);
     assert(blocks' % l = 0); (* comes from the spec of [split_at_last_lazy_nb_rem] *)
     Math.Lemmas.euclidean_division_definition blocks l;

     (* First, prove that the lengths of the rests are equal modulo the size of
     * a block *)
     assert(rest' % l = d % l); (* comes from the spec of [split_at_last] *)
     assert(rest + n * l = d);
     Math.Lemmas.lemma_mod_plus rest n l; (* doesn't work inside a calc: typing problem with squash *)
     assert(d % l = rest % l);
     assert(rest % l = rest' % l);

     (* If both rests are stricly smaller than a block, we can directly apply
      * the modulo injectivity and the rest follows immediately *)
     if rest < l && rest' < l then
       begin
       Math.Lemmas.lemma_mod_injective l rest rest';
       assert(rest = rest');
       assert(n * l + rest = n' * l + rest');
       assert(n * l = n' * l);
       Math.Lemmas.lemma_cancel_mul n n' l;
       assert(n = n')
       end
     (* Otherwise, case one: both rests are equal to block length (even easier) *)
     else if rest = l && rest' = l then
       Math.Lemmas.lemma_cancel_mul n n' l
     (* Last two cases: one of the rests is smaller than a block, and the other is
      * of the size of a block. Because of modulo properties, the smaller rest
      * must be equal to 0, which gives us that the data is actually of length 0:
      * contradiction. *)
     else
       begin
       assert((rest = l && rest' < l) \/ (rest < l && rest' = l));
       let rest, rest' = if rest = l then rest, rest' else rest', rest in
       assert(rest = l && rest' < l);
       (* [rest % l = 0] *)
       assert(rest = 1 * l);
       Math.Lemmas.cancel_mul_mod 1 l;
       assert(rest % l = 0);
       (* [rest' = 0 ] *)
       Math.Lemmas.modulo_lemma rest' l;
       assert(rest' = 0);
       (* By the current hypotheses, if rest' = 0 then d = 0 (contradiction) *)
       assert(False)
       end
     end
#pop-options

/// This second lemma characterizes the sequences themselves.
/// The proof strategy is to first prove that the blocks and rest sequences have
/// the expected lengths, and the equality between the sequences is then trivial
/// to get.
#push-options "--z3cliopt smt.arith.nl=false"
let split_at_last_lazy_spec (l : pos)
                            (b blocks rest: S.seq uint8):
  Lemma
  (requires (
    S.length blocks % l = 0 /\
    S.length rest <= l /\
    (S.length rest = 0 ==> S.length b = 0) /\
    b `Seq.equal` Seq.append blocks rest))
  (ensures (
     (blocks, rest) == split_at_last_lazy l b)) =
  (* We need to introduce the variables with which to call [split_at_last_lazy_nb_rem_spec] *)
  let b_l = Seq.length b in
  let blocks_l = Seq.length blocks in
  let rest_l = Seq.length rest in
  let blocks', rest' = split_at_last_lazy l b in
  let n' = Seq.length blocks' / l in
  let n = blocks_l / l in
  Math.Lemmas.nat_over_pos_is_nat blocks_l l;
  assert(n >= 0);
  Math.Lemmas.euclidean_division_definition (S.length blocks) l;
  split_at_last_lazy_nb_rem_spec l b_l n rest_l;
  assert(((n <: nat), rest_l) = split_at_last_lazy_nb_rem l b_l);
  assert(n = n'); (* comes from the spec of [split_at_last_lazy] *)
  assert(rest_l = Seq.length rest');
  (* We have the equalities between the sequence lengths, so the rest follows
   * naturally *)
  assert(blocks `Seq.equal` blocks');
  assert(rest `Seq.equal` rest')
#pop-options

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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 300"
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
