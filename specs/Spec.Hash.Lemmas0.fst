module Spec.Hash.Lemmas0

open Spec.Hash.Definitions

/// We need to put the following lemma in a file separate from Spec.Hash.Lemmas
/// in order to prevent circular dependencies between Spec.Hash.PadFinish and Spec.Hash.Lemmas

(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg{is_md a}): Lemma
  (ensures FStar.Mul.((max_input_length a) * 8 + 8 = pow2 (len_length a * 8)))
=
  let open FStar.Mul in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      assert_norm (max_input_length a * 8 + 8 = pow2 (len_length a * 8))
  | SHA2_384 | SHA2_512 ->
      assert_norm (max_input_length a * 8 + 8 = pow2 (len_length a * 8))
