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

#reset-options "--using_facts_from 'Prims Spec.Hash.Definitions'"
let pad_invariant_block (a: hash_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % block_length a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))
  [ SMTPat (pad_length a (blocks + rest)) ]
=
  //to prove: pad_length a rest == pad_length a (blocks + rest)
  //expanding pad_length:
  //          pad0_length a rest + 1 + len_length a == pad0_length a (blocks + rest) + 1 + len_length a
  //subtracting 1 + len_length a from both sides:
  //          pad0_length a rest == pad0_length a (blocks + rest)
  //expanding pad0_length:
  //          (block_length a - (rest + len_length a + 1)) % block_length a ==
  //          (block_length a - (blocks + rest + len_length a + 1)) % block_length a
  //
  //
  //say x = block_length a, and y = rest + len_length a + 1, then we have to prove:
  //
  //(x - y) % x == (x - (blocks + y)) % x -- G

  let x = block_length a in
  let y = rest + len_length a + 1 in

  FStar.Math.Lemmas.lemma_mod_sub_distr x y x;
  //gives us: (x - y) % x == (x - y%x) % x -- 1

  FStar.Math.Lemmas.lemma_mod_sub_distr x (blocks + y) x;
  //gives us: (x - (blocks + y)) % x == (x - (blocks + y)%x) % x -- 2
  
  FStar.Math.Lemmas.lemma_mod_add_distr y blocks x;
  //gives us: (y + blocks) % x == (y + blocks%x) % x
  //and since blocks%x == 0,
  //          (y + blocks) % x == y % x

  //which makes R.H.S. of (1) and (2) same, and hence the goal G

  ()
