module Spec.HMAC.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Lib.IntTypes
open Spec.Agile.HMAC

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let sized_key a = k:bytes { keysized a (Seq.length k) }

let hmac_extra_state (a:hash_alg) : extra_state a = match a with
  | Blake2B | Blake2S -> block_length a
  | _ -> allow_inversion hash_alg; ()

// Computes ipad xor key + feeds it into the hash
val init: a:fixed_len_alg -> key: sized_key a -> words_state a

// Compute first digest, compute opad, feed opad into second hash, feed hash sum
// into the second hash, write out second digest into destination. For the
// implementation, this function will either have to exhaustively specialize (as
// in EverCrypt.Hash), or perform a runtime allocation on the heap.
val finish:
  a: fixed_len_alg ->
  k: sized_key a ->
  h:words_state a ->
  lbytes (hash_length a)

let hmac_incremental
  (a: fixed_len_alg)
  (k: sized_key a)
  (data: bytes):
  Pure (lbytes (hash_length a))
    (requires (Seq.length data + block_length a) `less_than_max_input_length` a)
    (ensures fun _ -> True)
=
  let s = init a k in
  let bs, l = Spec.Hash.Incremental.Definitions.split_blocks a data in
  let s = Spec.Agile.Hash.update_multi a s (hmac_extra_state a) bs in
  let s = Spec.Hash.Incremental.Definitions.update_last a s (if is_keccak a then () else block_length a + S.length bs) l in
  finish a k s

val hmac_is_hmac_incremental (a: fixed_len_alg) (k: sized_key a) (data: bytes):
  Lemma
    (requires (Seq.length data + block_length a) `less_than_max_input_length` a)
    (ensures (S.equal (hmac a k data) (hmac_incremental a k data)))
