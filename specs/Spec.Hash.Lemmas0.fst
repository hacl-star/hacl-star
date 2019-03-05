module Spec.Hash.Lemmas0

open Spec.Hash.Definitions

(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg): Lemma
  (ensures FStar.Mul.(max_input_length a * 8 = pow2 (len_length a * 8)))
=
  let open FStar.Mul in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      assert_norm (max_input_length a * 8 = pow2 (len_length a * 8))
  | SHA2_384 | SHA2_512 ->
      assert_norm (max_input_length a * 8 = pow2 (len_length a * 8))

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 400"
let pad_invariant_block (a: hash_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % block_length a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))
  [ SMTPat (pad_length a (blocks + rest)) ]
=
  ()
