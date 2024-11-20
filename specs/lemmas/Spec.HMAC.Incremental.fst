module Spec.HMAC.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Lib.IntTypes
open Spec.Agile.HMAC

friend Spec.Agile.HMAC

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

// Processes exactly one block: the input key xored with the ipad
let init a k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let k = Spec.Agile.HMAC.wrap a k in
  Spec.Agile.Hash.update_multi a (Spec.Agile.Hash.init a) (Spec.Agile.Hash.init_extra_state a) (xor (u8 0x36) k)

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
let hmac_is_hmac_incremental a key data =
  (**) allow_inversion hash_alg;
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 125);
  let k = Spec.Agile.HMAC.wrap a key in
  (**) assert (S.length (xor (u8 0x36) k) == block_length a);
  (**) mod_mod a;
  let xored_k: bytes_blocks a = xor (u8 0x36) k in
  let h00 = update_multi a (Spec.Agile.Hash.init a) (init_extra_state a) xored_k in
  let blocks, last = Spec.Hash.Incremental.Definitions.split_blocks a data in
  (**) assert (S.length blocks % block_length a == 0);
  (**) FStar.Math.Lemmas.modulo_addition_lemma (S.length blocks) (block_length a) 1;
  (**) assert ((block_length a + S.length blocks) % block_length a == 0);

  let h01 = update_multi a h00 (hmac_extra_state a) blocks in
  let h02 = Spec.Hash.Incremental.Definitions.update_last a h01 (if is_keccak a then () else (block_length a + S.length blocks)) last in

  let h1 = Spec.Agile.Hash.finish a h02 () in
  let h2 = hash a (Seq.append (xor (u8 0x5c) k) h1) in

  (**) assert (h00 `S.equal` my_init a key);
  (**) assert (h2 `S.equal` my_finish a key h02);
  (**) assert (h2 `S.equal` hmac_incremental a key data);

  calc (S.equal) {
    h01;
  (S.equal) {}
    update_multi a (update_multi a (init a) (init_extra_state a) xored_k) (hmac_extra_state a) blocks;
  (S.equal) {
    if is_blake a then
      L.update_multi_associative_blake a (init a) 0 (block_length a) xored_k blocks
    else
      L.update_multi_associative a (init a) xored_k blocks
  }
    update_multi a (init a) (init_extra_state a) (xored_k `S.append` blocks);
  };

  let blocks', last' = Spec.Hash.Incremental.Definitions.split_blocks a (xored_k `S.append` data) in
  assume (S.equal blocks' (xored_k `S.append` blocks));
  assume (S.equal last last');

  calc (S.equal) {
    h1;
  (S.equal) {}
    Spec.Hash.Incremental.Definitions.hash_incremental a (xored_k `S.append` data) ();
  (S.equal) { Spec.Hash.Incremental.hash_is_hash_incremental' a (xored_k `S.append` data) () }
    hash' a (xored_k `S.append` data) ();
  (S.equal) { }
    hash a (xored_k `S.append` data);
  }
