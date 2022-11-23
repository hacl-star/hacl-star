module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas
open FStar.Mul

friend Spec.Agile.Hash

let blake2_is_hash_incremental a input =
  admit()

(* This proof works, but occasionally sends F* on an infinite loop.
   Commenting out for now
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
  (i:nat{i < S.length bs / block_length a}) (acc:words_state' a)
  : Lemma
     ( Spec.Blake2.blake2_update1 (to_blake_alg a) 0 input i acc == Spec.Blake2.blake2_update1 (to_blake_alg a) 0 bs i acc)
  = assert (Spec.Blake2.get_blocki (to_blake_alg a) input i `S.equal` Spec.Blake2.get_blocki (to_blake_alg a) bs i)

val blake2b_update_incremental
  (input : bytes {S.length input `less_than_max_input_length` Blake2B})
  (s: words_state' Blake2B & nat)
  : Lemma
    (requires snd s == 0)
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg Blake2B) 0 S.empty input (fst s))
              (let bs, l = split_blocks Blake2B input in
                let s:words_state' Blake2B & nat = update_multi Blake2B s bs in
                update_last Blake2B (fst s) (S.length bs) l))

/// Unclear why this proof needs to be spelled out more than the one for blake2s
let blake2b_update_incremental input s =
  let a = Blake2B in
  let a' = to_blake_alg Blake2B in

  let bs, l = split_blocks a input in
  let s_m:words_state' a & nat = update_multi a s bs in


  let nb = S.length bs / block_length a in

  let s_m_def = Lib.LoopCombinators.repeati nb (Spec.Blake2.blake2_update1 a' 0 bs) (fst s) in
  assert (fst s_m == s_m_def);

  Spec.Blake2.Alternative.lemma_spec_equivalence_update a' 0 S.empty input (fst s);

  assert ((S.empty `S.append` input) `S.equal` input);
  let nb', rem = Spec.Blake2.split a' (S.length input) in
  assert (S.length bs == nb' * block_length a);

  FStar.Math.Lemmas.cancel_mul_div (S.length bs) (block_length a);
  assert (nb == nb');
  let s_m' = Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 input) (fst s) in

  let aux () : Lemma (s_m' == Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 bs) (fst s))  =
    Classical.forall_intro_2 (update1_ext a input bs);
    Lib.Sequence.Lemmas.repeati_extensionality nb' (Spec.Blake2.blake2_update1 a' 0 input)
      (Spec.Blake2.blake2_update1 a' 0 bs) (fst s)
  in
  aux ();
  assert (s_m' == fst s_m)

val blake2s_update_incremental
  (input : bytes {S.length input `less_than_max_input_length` Blake2S})
  (s: words_state' Blake2S & nat)
  : Lemma
    (requires snd s == 0)
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg Blake2S) 0 S.empty input (fst s))
              (let bs, l = split_blocks Blake2S input in
                let s:words_state' Blake2S & nat = update_multi Blake2S s bs in
                update_last Blake2S (fst s) (S.length bs) l))


let blake2s_update_incremental input s =
  let a = Blake2S in
  let a' = to_blake_alg Blake2S in

  let bs, l = split_blocks a input in
  let s_m:words_state' a & nat = update_multi a s bs in

  let nb = S.length bs / block_length a in

  Spec.Blake2.Alternative.lemma_spec_equivalence_update a' 0 S.empty input (fst s);
  assert ((S.empty `S.append` input) `S.equal` input);

  let nb', rem = Spec.Blake2.split a' (S.length input) in
  assert (S.length bs == nb' * block_length a);
  FStar.Math.Lemmas.cancel_mul_div (S.length bs) (block_length a);
  assert (nb == nb');

  let s_m' = Lib.LoopCombinators.repeati nb' (Spec.Blake2.blake2_update1 a' 0 input) (fst s) in

  Lib.Sequence.Lemmas.repeati_extensionality nb (Spec.Blake2.blake2_update1 a' 0 input)
     (Spec.Blake2.blake2_update1 a' 0 bs) (fst s);
  assert (s_m' == fst s_m)

val blake2_update_incremental
  (a:blake_alg)
  (input : bytes {S.length input `less_than_max_input_length` a})
  (s: words_state' a & nat)
  : Lemma
    (requires snd s == 0)
    (ensures
      S.equal (Spec.Blake2.blake2_update (to_blake_alg a) 0 S.empty input (fst s))
              (let bs, l = split_blocks a input in
                let s:words_state' a & nat = update_multi a s bs in
                update_last a (fst s) (S.length bs) l))

let blake2_update_incremental a input s = match a with
  | Blake2B -> blake2b_update_incremental input s
  | Blake2S -> blake2s_update_incremental input s

let blake2_is_hash_incremental a input =
  let a' = to_blake_alg a in
  let n_blocks, l_last = Spec.Blake2.split a' (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (block_length a) input in
  let s_i = Spec.Blake2.blake2_init_hash a' 0 (Spec.Blake2.max_output (to_blake_alg a)) in
  let s_i': words_state' a & nat = init a in
  assert (s_i == fst s_i');

  blake2_update_incremental a input s_i'
*)
