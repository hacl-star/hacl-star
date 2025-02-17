module Spec.HMAC.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Lib.IntTypes
open Spec.Agile.HMAC

friend Spec.Agile.HMAC

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

// Processes exactly one block: the input key xored with the ipad
let init a k =
  let k = Spec.Agile.HMAC.wrap a k in
  let opad = xor (u8 0x5c) k in
  let empty_hash = Spec.Agile.Hash.init a in
  empty_hash, Spec.Agile.Hash.update_multi a empty_hash (Spec.Agile.Hash.init_extra_state a) opad

let init_input a k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let k = Spec.Agile.HMAC.wrap a k in
  xor (u8 0x36) k

let finish a k (first_hash2, second_hash1) =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let first_hash = Spec.Agile.Hash.finish a first_hash2 () in
  let second_hash2 = Spec.Hash.Incremental.Definitions.update_last a second_hash1 (if is_keccak a then () else block_length a) first_hash in
  Spec.Agile.Hash.finish a second_hash2 ()

unfold let my_init = init
unfold let my_finish = finish

(* Shadows init and finish *)
open Spec.Agile.Hash


let mod_mod (a: hash_alg): Lemma (block_length a % block_length a == 0) = allow_inversion hash_alg

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let block_length_fits (a: fixed_len_alg): Lemma ((pow2 32 - 1 + block_length a) `less_than_max_input_length` a) =
  assert (block_length a <= 168);
  assert_norm (pow2 32 + 168 <= pow2 61);
  assert_norm (pow2 32 + 168 <= pow2 125)
#pop-options

let block_and_hash_length_fits (a: fixed_len_alg): Lemma ((hash_length a + block_length a) `less_than_max_input_length` a) =
  assert (block_length a <= 168);
  assert (hash_length a <= pow2 32);
  assert_norm (pow2 32 + 168 <= pow2 61);
  assert_norm (pow2 32 + 168 <= pow2 125)

let split_lemma (a: fixed_len_alg):
  Lemma (Lib.UpdateMulti.split_at_last_lazy_nb_rem (block_length a) (block_length a + hash_length a) == (1, hash_length a))
=
  ()

let split_lemma2 (a: fixed_len_alg) (opad: bytes) (input: bytes): Lemma
  (requires S.length opad == block_length a /\ S.length input == hash_length a)
  (ensures (
    block_and_hash_length_fits a;
    let opad', input' = Spec.Hash.Incremental.Definitions.split_blocks a (opad `S.append` input) in
    opad == opad' /\ input == input'))
=
    block_and_hash_length_fits a;
    let opad', input' = Spec.Hash.Incremental.Definitions.split_blocks a (opad `S.append` input) in
    assert (opad `S.equal` opad');
    assert (input `S.equal` input')

#set-options "--fuel 0 --ifuel 0 --z3rlimit 400 --split_queries always"
let hmac_is_hmac_incremental a key input =
  (**) allow_inversion hash_alg;
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 125);
  let ipad = init_input a key in
  (**) assert (S.length ipad == block_length a);
  (**) mod_mod a;
  (**) Math.Lemmas.modulo_lemma 0 (block_length a);
  let opad: bytes_blocks a = xor (u8 0x5c) (Spec.Agile.HMAC.wrap a key) in

  let ipad: bytes_blocks a = ipad in
  let input1 = ipad `S.append` input in
  let bs, rest = Spec.Hash.Incremental.Definitions.split_blocks a input1 in

  let hash0 = init a in
  (**) assert (hash0 `S.equal` fst (my_init a key));
  let first_hash1 = update_multi a hash0 (init_extra_state a) bs in
  let first_hash2 = Spec.Hash.Incremental.Definitions.update_last a first_hash1 (if is_keccak a then () else (S.length bs)) rest in
  let second_hash1 = update_multi a hash0 (init_extra_state a) opad in
  (**) assert (second_hash1 `S.equal` snd (my_init a key));
  (**) assert (my_finish a key (first_hash2, second_hash1) `S.equal` hmac_incremental a key input);
  let first_hash = finish a first_hash2 () in
  (**) block_length_fits a;
  let second_hash2 =
    Spec.Hash.Incremental.Definitions.update_last a second_hash1 (if is_keccak a then () else block_length a) first_hash
  in
  let second_hash = finish a second_hash2 () in
  (**) assert (second_hash `S.equal` hmac_incremental a key input);

  calc (S.equal) {
    hmac_incremental a key input;
  (S.equal) {}
    second_hash;
  (S.equal) { Spec.Hash.Incremental.hash_is_hash_incremental' a input1 () }
    finish a (Spec.Hash.Incremental.Definitions.update_last a
      (update_multi a hash0 (Spec.Agile.Hash.init_extra_state a) opad)
      (if is_keccak a then () else block_length a)
      (hash' a input1 ())) ();
  (S.equal) { split_lemma a; split_lemma2 a opad (hash' a input1 ()) } (
    let opad, hash1 = Spec.Hash.Incremental.Definitions.split_blocks a (opad `S.append` (hash' a input1 ())) in
    finish a (Spec.Hash.Incremental.Definitions.update_last a
      (update_multi a (init a) (Spec.Agile.Hash.init_extra_state a) opad)
      (if is_keccak a then () else S.length opad)
      hash1) ()
  );
  (S.equal) { Spec.Hash.Incremental.hash_is_hash_incremental' a (opad `S.append` (hash' a input1 ())) () }
    hash' a (opad `S.append` (hash' a input1 ())) ();
  }
