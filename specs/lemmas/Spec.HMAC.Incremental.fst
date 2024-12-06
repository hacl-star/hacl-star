module Spec.HMAC.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Lib.IntTypes
open Spec.Agile.HMAC

friend Spec.Agile.HMAC

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

// Processes exactly one block: the input key xored with the ipad
let init a k =
  Spec.Agile.Hash.init a

let init_input a k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let k = Spec.Agile.HMAC.wrap a k in
  xor (u8 0x36) k

let finish a k s =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let k = wrap a k in
  let h1 = Spec.Agile.Hash.finish a s () in
  let h2 = Spec.Agile.Hash.hash a (Seq.append (xor (u8 0x5c) k) h1) in
  h2

unfold let my_init = init
unfold let my_finish = finish

(* Shadows init and finish *)
open Spec.Agile.Hash

module L = Spec.Hash.Lemmas

let mod_mod (a: hash_alg): Lemma (block_length a % block_length a == 0) = allow_inversion hash_alg

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let hmac_is_hmac_incremental a key input =
  (**) allow_inversion hash_alg;
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 125);
  let xored_k = init_input a key in
  (**) assert (S.length xored_k == block_length a);
  (**) mod_mod a;
  (**) Math.Lemmas.modulo_lemma 0 (block_length a);

  let xored_k: bytes_blocks a = xored_k in
  let input1 = xored_k `S.append` input in
  let bs, rest = Spec.Hash.Incremental.Definitions.split_blocks a input1 in

  let hash0 = init a in
  let hash1 = update_multi a hash0 (init_extra_state a) bs in
  let hash2 = Spec.Hash.Incremental.Definitions.update_last a hash1 (if is_keccak a then () else (S.length bs)) rest in
  let hash3 = finish a hash2 () in
  let hash4 = hash a ((xor (u8 0x5c) (wrap a key)) `S.append` hash3) in
  (**) assert (hash4 `S.equal` hmac_incremental a key input);

  calc (S.equal) {
    hash3;
  (S.equal) { Spec.Hash.Incremental.hash_is_hash_incremental' a input1 () }
    hash' a input1 ();
  }
