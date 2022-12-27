module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.Lemmas
open FStar.Mul

friend Spec.Agile.Hash

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
// let blake2_is_hash_incremental a input =
//   let blocks, last = Lib.UpdateMulti.split_at_last_lazy (block_length a) input in
//   let s = init a in

//   let a = to_blake_alg a in
//   let n_blocks, l_last = Spec.Blake2.split a (S.length input) in
//   let s1 = Lib.LoopCombinators.repeati n_blocks (Spec.Blake2.blake2_update1 a 0 input) s in
//   let s2 = Lib.LoopCombinators.repeati n_blocks (Spec.Blake2.blake2_update1 a 0 blocks) s in
//   Lib.Sequence.Lemmas.repeati_extensionality n_blocks (Spec.Blake2.blake2_update1 a 0 input)
//     (Spec.Blake2.blake2_update1 a 0 blocks) s;
//   S.lemma_eq_intro (S.slice input (S.length input - l_last) (S.length input)) last;
//   S.lemma_eq_intro (S.slice last (S.length last - l_last) (S.length last)) last


/// AF: While this proof should be conceptually simple, and very similar to the proof in Hacl.Streaming.Blake2,
/// F* struggles heavily with the dependent pairs for the state and slighty type mismatches...
/// In particular, even proving that update_multi is equal to its definition can be challenging.
/// The workaround is to do the proof duplication below. Providing a concrete value for the algorithm allows F*
/// to normalize definitions further, and simplifies the automatic proof of previously tricky equalities

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let update1_ext
  (a:blake_alg)
  (input:bytes{S.length input `less_than_max_input_length` a})
  (bs:bytes{bs == fst (split_blocks a input)})
  (i:nat{i < S.length bs / block_length a}) (acc:words_state a)
  : Lemma
     ( Spec.Blake2.blake2_update1 (to_blake_alg a) 0 input i acc == Spec.Blake2.blake2_update1 (to_blake_alg a) 0 bs i acc)
  = assert (Spec.Blake2.get_blocki (to_blake_alg a) input i `S.equal` Spec.Blake2.get_blocki (to_blake_alg a) bs i)

val blake2b_update_incremental
  (input : bytes {S.length input `less_than_max_input_length` Blake2B})
  (s: words_state Blake2B)
  : Lemma
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg Blake2B) 0 S.empty input s)
              (let bs, l = split_blocks Blake2B input in
                let s:words_state Blake2B = update_multi Blake2B s 0 bs in
                update_last Blake2B s (S.length bs) l))

/// Unclear why this proof needs to be spelled out more than the one for blake2s
let blake2b_update_incremental input s =
  let a = Blake2B in
  let a' = to_blake_alg Blake2B in

  let bs, l = split_blocks a input in
  let s_m:words_state a = update_multi a s 0 bs in


  let nb = S.length bs / block_length a in

  let s_m_def = Lib.LoopCombinators.repeati nb (Spec.Blake2.blake2_update1 a' 0 bs) s in
  assert (s_m == s_m_def);

  Spec.Blake2.Alternative.lemma_spec_equivalence_update a' 0 S.empty input s;

  assert ((S.empty `S.append` input) `S.equal` input);
  let nb', rem = Spec.Blake2.split a' (S.length input) in
  assert (S.length bs == nb' * block_length a);

  FStar.Math.Lemmas.cancel_mul_div (S.length bs) (block_length a);
  assert (nb == nb');
  let s_m' = Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 input) s in

  let aux () : Lemma (s_m' == Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 bs) s)  =
    Classical.forall_intro_2 (update1_ext a input bs);
    Lib.Sequence.Lemmas.repeati_extensionality nb' (Spec.Blake2.blake2_update1 a' 0 input)
      (Spec.Blake2.blake2_update1 a' 0 bs) s
  in
  aux ();
  assert (s_m' == s_m)

val blake2s_update_incremental
  (input : bytes {S.length input `less_than_max_input_length` Blake2S})
  (s: words_state Blake2S)
  : Lemma
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg Blake2S) 0 S.empty input s)
              (let bs, l = split_blocks Blake2S input in
                let s:words_state Blake2S = update_multi Blake2S s 0 bs in
                update_last Blake2S s (S.length bs) l))

let blake2s_update_incremental input s =
  let a = Blake2S in
  let a' = to_blake_alg Blake2S in

  let bs, l = split_blocks a input in
  let s_m:words_state a = update_multi a s 0 bs in

  let nb = S.length bs / block_length a in

  Spec.Blake2.Alternative.lemma_spec_equivalence_update a' 0 S.empty input s;
  assert ((S.empty `S.append` input) `S.equal` input);

  let nb', rem = Spec.Blake2.split a' (S.length input) in
  assert (S.length bs == nb' * block_length a);
  FStar.Math.Lemmas.cancel_mul_div (S.length bs) (block_length a);
  assert (nb == nb');

  let s_m' = Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 input) s in

  Lib.Sequence.Lemmas.repeati_extensionality nb (Spec.Blake2.blake2_update1 a' 0 input)
     (Spec.Blake2.blake2_update1 a' 0 bs) s;
  assert (s_m' == s_m)

val blake2_update_incremental
  (a:blake_alg)
  (input : bytes {S.length input `less_than_max_input_length` a})
  (s: words_state a)
  : Lemma
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg a) 0 S.empty input s)
              (let bs, l = split_blocks a input in
                let s:words_state a = update_multi a s 0 bs in
                update_last a s (S.length bs) l))

let blake2_update_incremental a input s = match a with
  | Blake2B -> blake2b_update_incremental input s
  | Blake2S -> blake2s_update_incremental input s

let blake2_is_hash_incremental a input =
  let a' = to_blake_alg a in
  let n_blocks, l_last = Spec.Blake2.split a' (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (block_length a) input in
  let s_i = Spec.Blake2.blake2_init_hash a' 0 (Spec.Blake2.max_output (to_blake_alg a)) in
  let s_i': words_state a = init a in
  assert (s_i == s_i');

  blake2_update_incremental a input s_i'
