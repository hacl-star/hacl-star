module Spec.Hash.Lemmas0

open Spec.Hash.Definitions

let block_length_smaller_than_max_input (a:hash_alg) :
  Lemma(block_length a <= max_input_length a) =
  normalize_term_spec(pow2 61 - 1);
  normalize_term_spec(pow2 125 - 1);
  normalize_term_spec(pow2 64 - 1)

(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg{not (is_blake a)}): Lemma
  (ensures FStar.Mul.((max_input_length a) * 8 + 8 = pow2 (len_length a * 8)))
=
  let open FStar.Mul in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      assert_norm (max_input_length a * 8 + 8 = pow2 (len_length a * 8))
  | SHA2_384 | SHA2_512 ->
      assert_norm (max_input_length a * 8 + 8 = pow2 (len_length a * 8))

#reset-options "--using_facts_from 'Prims Spec.Hash.Definitions'"
#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let pad_invariant_block (a: hash_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % block_length a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))
  [ SMTPat (pad_length a (blocks + rest)) ]
= 
  match a with
  | Blake2S | Blake2B ->
    calc (==) {
      (pad_length a (blocks + rest) <: int);
    (==) {}
      (block_length a - blocks - rest) % block_length a;
    (==) {}
      ((block_length a - rest) - blocks) % block_length a;
    (==) { Math.Lemmas.lemma_mod_sub_distr (block_length a - rest) blocks (block_length a) }
      (block_length a - rest) % block_length a;
    (==) {}
      pad_length a rest;
    }
  | _ ->
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

  Math.Lemmas.lemma_mod_sub_distr x y x;
  //gives us: (x - y) % x == (x - y%x) % x -- 1

  Math.Lemmas.lemma_mod_sub_distr x (blocks + y) x;
  //gives us: (x - (blocks + y)) % x == (x - (blocks + y)%x) % x -- 2

  Math.Lemmas.lemma_mod_add_distr y blocks x;
  //gives us: (y + blocks) % x == (y + blocks%x) % x
  //and since blocks%x == 0,
  //          (y + blocks) % x == y % x

  //which makes R.H.S. of (1) and (2) same, and hence the goal G

  ()
#pop-options

let pad_length (a: hash_alg) (len: nat): Tot (n:nat { (len + n) % block_length a = 0 }) =
  if is_blake a then (block_length a - len) % block_length a
  else pad0_length a len + 1 + len_length a
