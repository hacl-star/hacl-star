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

/// TODO: A lemma I could not find in FStar.Math.Lemmas
/// Note: duplicated in Hash.Streaming.Spec.fst and Spec.Hash.Incremental
let mul_zero_left_is_zero (n : int) : Lemma(0 * n = 0) = ()

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
      (**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
      Spec.Hash.Incremental.update_last a s 0 input ==
      Spec.Hash.Incremental.hash_incremental_body a input s) =
  (**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
  let bs, l = split_blocks a input in
  assert(bs `Seq.equal` Seq.empty);
  assert(l `Seq.equal` input);
  Spec.Hash.Lemmas.update_multi_zero a s

let block_hash_incremental (a:hash_alg) (input:bytes_block a)
  : Lemma
    ((**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
     finish a (update_last a (init a) 0 input) `S.equal` hash_incremental a input) =
  (**) Spec.Hash.Lemmas0.block_length_smaller_than_max_input a;
  hash_incremental_block_is_update_last a (init a) input

#push-options "--z3cliopt smt.arith.nl=false"
let lemma_split_blocks_assoc (a:hash_alg) (s1 s2:bytes)
  : Lemma
      (requires
        S.length s1 + S.length s2 <= max_input_length a /\
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

  mul_zero_left_is_zero (block_length a);
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

let lemma_split_blake_modulo (a:hash_alg{is_blake a}) (s1 s2:bytes)
  : Lemma
      (requires S.length s1 + S.length s2 <= max_input_length a /\
        S.length s1 % block_length a == 0 /\ S.length s2 > 0)
      (ensures (
        let b1, l1, rem1 = last_split_blake a (s1 `S.append` s2) in
        let b2, l2, rem2 = last_split_blake a s2 in
        l1 == l2 /\ rem1 == rem2)
      )
   = lemma_split_blocks_assoc a s1 s2

let compose_split_blocks (a:hash_alg{is_blake a}) (inp1:bytes) (inp2:bytes)
  : Lemma
    (requires S.length inp1 % block_length a == 0 /\
      S.length inp2 > 0 /\
      S.length inp1 + S.length inp2 <= max_input_length a)
    (ensures (
      let input = inp1 `Seq.append` inp2 in
      let bs, l = split_blocks a input in
      let _, last, _ = last_split_blake a l in
      let blocks2, last2, rem2 = last_split_blake a inp2 in
      last == last2 /\
      bs == inp1 `S.append` blocks2 /\
      rem2 == S.length l))
  = let input = inp1 `Seq.append` inp2 in
    let bs, l = split_blocks a input in
    let _, last, _ = last_split_blake a l in
    let blocks2, last2, rem2 = last_split_blake a inp2 in
    lemma_split_blocks_assoc a inp1 inp2;
    let b2, _ = split_blocks a inp2 in
    lemma_split_blake_modulo a b2 l

let concatenated_hash_incremental_blake_aux (a:hash_alg{is_blake a})
  (inp1:bytes) (inp2:bytes)
  (h:words_state a)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\
      Seq.length inp1 % block_length a == 0 /\ Seq.length inp2 > 0)
    (ensures (
      let input = inp1 `S.append` inp2 in
      let bs, l = split_blocks a input in
      fst (update_last_blake a (update_multi a h bs) (S.length bs) l) ==
      fst (update_last_blake a (update_multi a h inp1) (S.length inp1) inp2)))
  = let input = inp1 `S.append` inp2 in
    let bs, l = split_blocks a input in
    let blocks2, last2, rem2 = last_split_blake a inp2 in
    let h1 = update_multi a (update_multi a h inp1) blocks2 in
    let h_f = update_last_blake a h1 (S.length bs) l in
    let h2 = extra_state_add_nat (snd h1) rem2 in
    let h_f2 = Spec.Blake2.blake2_update_block (to_blake_alg a) true
                                               (extra_state_v h2)
                                               last2 (fst h1) in

    let _, last, _ = last_split_blake a l in
    compose_split_blocks a inp1 inp2;

    Spec.Hash.Lemmas.update_multi_associative a h inp1 blocks2;
    assert (h1 == update_multi a h bs)


let concatenated_hash_incremental_blake (a:hash_alg{is_blake a}) (inp1:bytes) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\
      Seq.length inp1 % block_length a == 0 /\ Seq.length inp2 > 0)
    (ensures finish a (update_last_blake a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
  = let open FStar.Mul in
    let h = init a in
    concatenated_hash_incremental_blake_aux a inp1 inp2 h

let concatenated_hash_incremental_md_aux (a:hash_alg{is_md a})
  (inp1:bytes) (inp2:bytes)
  (h:words_state a)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\
      Seq.length inp1 % block_length a == 0 /\ Seq.length inp2 > 0)
    (ensures (
      let input = inp1 `S.append` inp2 in
      let bs, l = split_blocks a input in
      fst (update_last a (update_multi a h bs) (S.length bs) l) ==
      fst (update_last a (update_multi a h inp1) (S.length inp1) inp2)))
  = allow_inversion hash_alg;
    let input = inp1 `S.append` inp2 in
    let bs, l = split_blocks a input in
    let total_len = S.length bs + S.length l in
    let padding = pad a total_len in
    let l_padded = l `S.append` padding in
    calc (==) {
      (S.length padding + total_len) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) total_len (block_length a) }
      (S.length padding + total_len % block_length a) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length l) (S.length bs) (block_length a) }
      (S.length padding + S.length l % block_length a) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) (S.length l) (block_length a) }
      S.length l_padded % block_length a;
    };
    let l2_padded = inp2 `S.append` padding in
    calc (==) {
      (S.length padding + total_len) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) total_len (block_length a) }
      (S.length padding + total_len % block_length a) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length inp2) (S.length inp1) (block_length a) }
      (S.length padding + S.length inp2 % block_length a) % block_length a;
      (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) (S.length inp2) (block_length a) }
      S.length l2_padded % block_length a;
    };

    calc (==) {
      update_last a (update_multi a h bs) (S.length bs) l;
      (==) { }
      update_multi a (update_multi a h bs) l_padded;
      (==) { Spec.Hash.Lemmas.update_multi_associative a h bs l_padded }
      update_multi a h (bs `S.append` l_padded);
      (==) { S.append_assoc bs l padding }
      update_multi a h (input `S.append` padding);
      (==) { S.append_assoc inp1 inp2 padding }
      update_multi a h (inp1 `S.append` (inp2 `S.append` padding));
      (==) { Spec.Hash.Lemmas.update_multi_associative a h inp1 (inp2 `S.append` padding) }
      update_last a (update_multi a h inp1) (S.length inp1) inp2;
    }

let concatenated_hash_incremental_md (a:hash_alg{is_md a}) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ S.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
  = let h = init a in
    concatenated_hash_incremental_md_aux a inp1 inp2 h

let concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires S.length (inp1 `S.append` inp2) <= max_input_length a /\ S.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
   = if is_blake a then concatenated_hash_incremental_blake a inp1 inp2
     else concatenated_hash_incremental_md a inp1 inp2
