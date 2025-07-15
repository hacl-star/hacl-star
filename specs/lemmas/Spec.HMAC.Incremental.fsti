module Spec.HMAC.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Lib.IntTypes
open Spec.Agile.HMAC

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let sized_key a = k:bytes { keysized a (Seq.length k) }

let hmac_extra_state (a:hash_alg) : extra_state a = match a with
  | Blake2B | Blake2S -> block_length a
  | _ -> allow_inversion hash_alg; ()

let hmac_state a = words_state a & words_state a

// We adopt the more complicated init / init_input form of incrementality
// defined rather recently in the streaming functor for the needs of Blake2. In
// this style, init_input_s captures the initial input that needs to be fed into
// the incremental algorithm, with the understanding that it might be the only
// input. This saves the need for an excruciating case analysis in the
// hmac_incremental definition below, and awful reasoning on split_blocks.
val init: a:fixed_len_alg -> key: sized_key a -> hmac_state a

// To understand the intent behind this peculiar style of specification, it
// suffices to look at Hacl.Streaming.Interface.fsti -- we're simply trying to
// meet this interface, and prove the central "spec is incremental" lemma
// expected by this functor.
let init_input_length a = block_length a

// This one computes the ipad xored with the key. Think of it as a "pre-input".
val init_input: a:fixed_len_alg -> key: sized_key a -> b:bytes { S.length b == init_input_length a }

// Compute first digest, compute opad, feed opad into second hash, feed hash sum
// into the second hash, write out second digest into destination. For the
// implementation, this function will either have to exhaustively specialize (as
// in EverCrypt.Hash), or perform a runtime allocation on the heap.
val finish:
  a: fixed_len_alg ->
  k: sized_key a ->
  h: hmac_state a ->
  lbytes (hash_length a)

// This definition is *exactly* in the style expected by Hacl.Streaming.Interface.spec_is_incremental
let hmac_incremental
  (a: fixed_len_alg)
  (k: sized_key a)
  (input: bytes):
  Pure (lbytes (hash_length a))
    (requires (Seq.length input + init_input_length a) `less_than_max_input_length` a)
    (ensures fun _ -> True)
=
  let input1 = S.append (init_input a k) input in
  let bs, rest = Spec.Hash.Incremental.Definitions.split_blocks a input1 in
  (**) Math.Lemmas.modulo_lemma 0 (block_length a);
  let hash0, second_hash = init a k in
  let hash1 = Spec.Agile.Hash.update_multi a hash0 (Spec.Agile.Hash.init_extra_state a) bs in
  let hash2 =
    Spec.Hash.Incremental.Definitions.update_last a hash1 (if is_keccak a then () else S.length bs) rest
  in
  finish a k (hash2, second_hash)

val hmac_is_hmac_incremental (a: fixed_len_alg) (k: sized_key a) (data: bytes):
  Lemma
    (requires (Seq.length data + block_length a) `less_than_max_input_length` a)
    (ensures (S.equal (hmac a k data) (hmac_incremental a k data)))
