module Spec.Hash.Lemmas

module S = FStar.Seq
open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

friend Spec.Agile.Hash

let extra_state_add_nat_bound_lem1 (#a:hash_alg{is_blake a}) (s : extra_state a)
                                   (n:nat{n <= max_extra_state a}) :
  Lemma
  (requires extra_state_v s + n <= max_extra_state a)
  (ensures extra_state_v (extra_state_add_nat s n) = extra_state_v s + n) = ()

let extra_state_add_nat_bound_lem2 (#a:hash_alg{is_blake a}) (s : extra_state a)
                                   (n:nat{n <= max_extra_state a}) :
  Lemma
  (requires extra_state_v s + n <= max_extra_state a)
  (ensures extra_state_add_nat s n == nat_to_extra_state a ((extra_state_v s) + n)) =
  assert(v ((s <: extra_state_int_t a) +. nat_to_extra_state a n) = extra_state_v s + n);
  ()

let extra_state_add_nat_bound_associative_lem (#a:hash_alg{is_blake a}) (s : extra_state a)
                                              (n1 n2 : range_t (extra_state_int_type a)) :
  Lemma
  (requires n1 + n2 <= max_extra_state a)
  (ensures
       (extra_state_add_nat (extra_state_add_nat s n1) n2 ==
        extra_state_add_nat s (n1 + n2))) =
  let s1 = extra_state_add_nat s n1 in
  let s2 = extra_state_add_nat s1 n2 in
  let s3 = extra_state_add_nat s (n1 + n2) in
  let s1_v = extra_state_v s1 in
  let s2_v = extra_state_v s2 in
  let s3_v = extra_state_v s3 in
  let t = extra_state_int_type a in
  assert(s1_v == (extra_state_v s + n1) @%. t);
  assert(s2_v == s1_v + n2 @%. t);
  assert(s2_v == (s1_v + n2) % modulus t);
  Math.Lemmas.lemma_mod_add_distr n2 (extra_state_v s + n1) (modulus t);
  assert(s2_v == (extra_state_v s + n1 + n2) % modulus t);
  Math.Lemmas.lemma_mod_add_distr (extra_state_v s) (n1 + n1) (modulus t);
  assert(s3_v == (extra_state_v s + n1 + n2) % modulus t);
  assert(s2_v == s3_v)

let extra_state_v_of_nat (a:hash_alg{is_blake a})
                         (n:nat{n <= max_extra_state a}) :
  Lemma(extra_state_v (nat_to_extra_state a n) = n) = ()

(* Lemmas such as: relationship between maximum lengths, incremental API vs.
 * NIST reference, etc. *)

(** Lemmas about the behavior of update_multi / update_last *)

let update_multi_zero (a: hash_alg) = Lib.UpdateMulti.update_multi_zero (block_length a) (Spec.Agile.Hash.update a)

#push-options "--fuel 1"
let update_multi_update (a: hash_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (update_multi a h input) == (update a h input))
=
  let h1 = update_multi a h input in
  assert(h1 == Lib.UpdateMulti.mk_update_multi (block_length a) (update a) h input);
  if S.length input = 0 then
    begin
    assert(h1 == h)
    end
  else
    begin
    let block, rem = Lib.UpdateMulti.split_block (block_length a) input 1 in
    let h2 = update a h block in
    assert(rem `Seq.equal` Seq.empty);
    assert(block `Seq.equal` input);
    let h3 = Lib.UpdateMulti.mk_update_multi (block_length a) (update a) h2 rem in
    assert(h1 == h3)
    end
#pop-options

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

(* *)
let block_length_smaller_than_max_input (a:hash_alg) :
  Lemma(block_length a <= max_input_length a) =
  normalize_term_spec(pow2 61 - 1);
  normalize_term_spec(pow2 125 - 1);
  normalize_term_spec(pow2 64 - 1)
  
#reset-options "--using_facts_from 'Prims Spec.Hash.Definitions'"
#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let pad_invariant_block (a: hash_alg) (blocks: nat) (rest: nat): Lemma
  (requires blocks % block_length a = 0)
  (ensures (pad_length a rest = pad_length a (blocks + rest)))
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

(* A useful lemma for all the operations that involve going from bytes to bits. *)
let max_input_size_len (a: hash_alg{is_md a}):
  Lemma (FStar.Mul.((max_input_length a) * 8 + 8 = pow2 (len_length a * 8)))
=
  let open FStar.Mul in
  (* Small trick to ensure proper normalization: depending on the algorithm
   * there are two possible values for the max input length. However, we need
   * to normalize the quantities on specific algorithm values, otherwise the
   * prover fails. *)
  let f a = Spec.Hash.Definitions.max_input_length a * 8 + 8 = pow2 (Spec.Hash.Definitions.len_length a * 8) in
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> assert_norm(f MD5)
  | SHA2_384 | SHA2_512 -> assert_norm(f SHA2_384)
