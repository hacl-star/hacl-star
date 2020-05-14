module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

friend Spec.Agile.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) d 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a d)
  = admit()

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
=
  if is_blake a then (blake2_is_hash_incremental a input)
  else
  admit();
  let open FStar.Mul in
  let n = S.length input / block_length a in
  let padding = pad a (S.length input) in
  let padded_input = input `S.append` padding in
  let blocks, rest = Lib.UpdateMulti.split_block (block_length a) padded_input n in
  let blocks', rest' = S.split input (n * block_length a) in
  S.lemma_eq_intro blocks blocks';
  S.lemma_eq_intro (rest' `S.append` padding) rest;
  Math.Lemmas.multiple_modulo_lemma n (block_length a);
  S.lemma_eq_intro padded_input (blocks `S.append` rest);
  update_multi_associative a (init a) blocks rest;
  S.lemma_eq_intro (fst (update_multi a (init a) padded_input)) (fst (update_multi a (update_multi a (init a) blocks) rest))
