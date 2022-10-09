module Spec.Hash.Incremental.Lemmas

open Spec.Agile.Hash
open Spec.Hash.PadFinish

open FStar.Mul
open Lib.IntTypes

open Spec.Agile.Hash
friend Spec.Agile.Hash
open Spec.Hash.Lemmas
open Spec.Hash.Incremental

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let update_multi_empty_extra_state_eq
  (a: hash_alg{is_blake a}) (h: words_state a) :
  Lemma
  (requires True)
  (ensures
    (snd (update_multi a h Seq.empty) == extra_state_add_nat (snd h) 0)) =
  let ev = snd h in
  let ev_v = extra_state_v ev in
  assert(ev_v <= max_extra_state a);
  assert(ev_v + 0 = ev_v);
  assert(ev_v + 0 <= max_extra_state a);
  Spec.Hash.Lemmas.update_multi_zero a h;
  assert(Seq.length (Seq.empty #uint8) = 0);
  Math.Lemmas.modulo_lemma 0 (block_length a);
  assert(update_multi a h Seq.empty == h);
  extra_state_add_nat_bound_lem1 ev 0

let rec update_multi_extra_state_eq
  (a: hash_alg{is_blake a}) (h: words_state a)
  (input: bytes_blocks a{Seq.length input <= max_extra_state a}) :
  Lemma
  (requires True)
  (ensures
    (snd (update_multi a h input) == extra_state_add_nat (snd h) (Seq.length input)))
  (decreases (Seq.length input)) =
  if Seq.length input = 0 then
    begin
    assert(input `Seq.equal` Seq.empty);
    update_multi_empty_extra_state_eq a h
    end
  else
    begin
    let input1 = Seq.slice input 0 (block_length a) in
    let input2 = Seq.slice input (block_length a) (Seq.length input) in
    assert(input `Seq.equal` Seq.append input1 input2);
    assert(Seq.length input1 % block_length a == 0);
    assert(Seq.length input2 % block_length a == 0);
    Spec.Hash.Lemmas.update_multi_associative a h input1 input2;
    let h1 = update_multi a h input1 in
    Spec.Hash.Lemmas.update_multi_update a h input1;
    assert(Seq.length input2 < Seq.length input);
    assert(snd h1 == extra_state_add_nat (snd h) (block_length a));
    let h2 = update_multi a h1 input2 in
    assert(h2 == update_multi a h input);
    update_multi_extra_state_eq a h1 input2;
    assert(snd h2 == extra_state_add_nat (snd h1) (Seq.length input2));
    extra_state_add_nat_bound_associative_lem (snd h) (Seq.length input1) (Seq.length input2)
    end

let hash_incremental_block_is_update_last (a:hash_alg)
  (s:words_state a)
  (input : bytes_block a) :
  Lemma (
      (**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
      Spec.Hash.Incremental.update_last a s 0 input ==
      Spec.Hash.Incremental.hash_incremental_body a input s) =
  (**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
  let bs, l = split_blocks a input in
  assert(bs `Seq.equal` Seq.empty);
  assert(l `Seq.equal` input);
  Spec.Hash.Lemmas.update_multi_zero a s

let block_hash_incremental (a:hash_alg) (input:bytes_block a)
  : Lemma
    ((**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
     finish a (update_last a (init a) 0 input) `S.equal` hash_incremental a input) =
  (**) Spec.Hash.Lemmas.block_length_smaller_than_max_input a;
  hash_incremental_block_is_update_last a (init a) input

#push-options "--z3cliopt smt.arith.nl=false"
let lemma_split_blocks_assoc (a:hash_alg) (s1 s2:bytes)
  : Lemma
      (requires
        (S.length s1 + S.length s2) `less_than_max_input_length` a /\
        S.length s1 % block_length a == 0 /\ S.length s2 > 0)
      (ensures (
        let b1, l1 = split_blocks a (s1 `S.append` s2) in
        let b2, l2 = split_blocks a s2 in
        b1 == s1 `S.append` b2 /\ l1 == l2)) =
  let s = s1 `S.append` s2 in
  let n_s1 = S.length s1 / block_length a in

  let n1 = S.length s / block_length a in
  let n2 = S.length s2 / block_length a in

  Math.Lemmas.euclidean_division_definition (S.length s1) (block_length a);
  assert(S.length s1 = (S.length s1 / block_length a) * block_length a);
  Math.Lemmas.division_addition_lemma (S.length s2) (block_length a) n_s1;
  assert (n1 == n2 + n_s1);

  Math.Lemmas.mul_zero_left_is_zero (block_length a);
  Math.Lemmas.nat_over_pos_is_nat (S.length s) (block_length a);
  Math.Lemmas.euclidean_division_definition (S.length s) (block_length a);
  assert(S.length s % block_length a = 0 ==> n1 > 0);

  Math.Lemmas.nat_over_pos_is_nat (S.length s2) (block_length a);
  Math.Lemmas.euclidean_division_definition (S.length s2) (block_length a);
  assert(S.length s2 % block_length a = 0 ==> n2 > 0);

  let n1' = if S.length s % block_length a = 0 then n1-1 else n1 in
  let n2' = if S.length s2 % block_length a = 0 then n2-1 else n2 in

  Math.Lemmas.nat_times_nat_is_nat n1' (block_length a);
  Math.Lemmas.lemma_mult_le_right (block_length a) n1' n1;
  Math.Lemmas.nat_times_nat_is_nat n2' (block_length a);
  Math.Lemmas.lemma_mult_le_right (block_length a) n2' n2;
  let bs1, ls1 = S.split s (n1' * block_length a) in
  let bs2, ls2 = S.split s2 (n2' * block_length a) in
  
  Math.Lemmas.lemma_mod_add_distr (S.length s2) (S.length s1) (block_length a);
  assert(S.length s % block_length a = S.length s2 % block_length a);
  assert(n_s1 * block_length a = S.length s1);
  
  if S.length s % block_length a = 0 then
    begin
    Math.Lemmas.distributivity_sub_left n1 1 (block_length a);
    Math.Lemmas.distributivity_sub_left n2 1 (block_length a)
    end;
  
  assert (n1' * block_length a == n2' * block_length a + S.length s1);
  assert (S.equal ls1 ls2);
  assert (S.equal bs1 (s1 `S.append` bs2))
#pop-options
