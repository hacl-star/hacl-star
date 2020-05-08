module Spec.Hash.Lemmas

module S = FStar.Seq

include Spec.Hash.Lemmas0

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental
open Spec.Hash.PadFinish

friend Spec.Agile.Hash

(* Lemmas such as: relationship between maximum lengths, incremental API vs.
 * NIST reference, etc. *)

(** Lemmas about the behavior of update_multi / update_last *)

let update_multi_zero (a: hash_alg) = Lib.UpdateMulti.update_multi_zero (block_length a) (Spec.Agile.Hash.update a)

let update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (update_multi a h input) == (update a h input))
=
  ()

let update_multi_associative (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    (update_multi a (update_multi a h input1) input2) ==
      (update_multi a h input)))
=
  Lib.UpdateMulti.update_multi_associative (block_length a) (Spec.Agile.Hash.update a) h input1 input2

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) d 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)) ==
     Spec.Hash.Incremental.hash_incremental a d)
  = admit()

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
=
  if is_blake a then blake2_is_hash_incremental a input
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

#push-options "--z3rlimit 100"

let concatenated_hash_incremental_md (a:hash_alg{is_md a}) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` Spec.Hash.Incremental.hash_incremental a (inp1 `S.append` inp2))
  = admit();
    allow_inversion hash_alg;
    let len = S.length inp2 in
    calc (S.equal) {
    finish a (update_last a (update_multi a (init a) inp1)
        (S.length inp1) inp2);
    (S.equal) { }
      finish a (update_multi a (update_multi a (init a) inp1)
        (S.append inp2 (pad a (S.length inp1 + len))));
    (S.equal) { }
      finish a (update_multi a (init a)
        (S.append inp1
          (S.append inp2 (pad a (S.length inp1 + len)))));
    (S.equal) { S.append_assoc
      inp1
      inp2
      (pad a (S.length inp1 + len))
    }
      finish a (update_multi a (init a)
        (S.append (S.append inp1 inp2)
          (pad a (S.length inp1 + len))));
    (==) { }
      Spec.Agile.Hash.hash a (S.append inp1 inp2);
    };
    hash_is_hash_incremental a (S.append inp1 inp2)

#pop-options

let concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` Spec.Hash.Incremental.hash_incremental a (inp1 `S.append` inp2))
   = if is_blake a then admit() // proven in Spec.Hash.Incremental, todo, reorganize
     else concatenated_hash_incremental_md a inp1 inp2
