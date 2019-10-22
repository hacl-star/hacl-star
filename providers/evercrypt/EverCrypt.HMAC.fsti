(** Agile HMAC *)
module EverCrypt.HMAC

module B = LowStar.Buffer

open Spec.Agile.HMAC
open Spec.Hash.Definitions

open FStar.HyperStack.ST
open Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

/// Auxiliary lemma

let key_and_data_fits (a: hash_alg): Lemma
  (ensures (block_length a + pow2 32 <= max_input_length a))
=
  let open FStar.Mul in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

/// Type for compute
/// Duplicated from Hacl.HMAC because we don't want clients to depend on Hacl.HMAC

inline_for_extraction
let compute_st (a: hash_alg) =
  tag: B.buffer uint8 {B.length tag == hash_length a} ->
  key: B.buffer uint8{ keysized a (B.length key) /\ B.disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = B.length key } ->
  // Can we have max_input_length a instead of pow2 32?
  data: B.buffer uint8{ B.length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = B.length data } ->
  Stack unit
  (requires fun h0 -> B.live h0 tag /\ B.live h0 key /\ B.live h0 data)
  (ensures  fun h0 _ h1 ->
    key_and_data_fits a;
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    B.as_seq h1 tag == hmac a (B.as_seq h0 key) (B.as_seq h0 data))

/// Four monomorphized variants, for callers who already know which algorithm they want

(** @type: true
*)
val compute_sha1: compute_st SHA1

(** @type: true
*)
val compute_sha2_256: compute_st SHA2_256

(** @type: true
*)
val compute_sha2_384: compute_st SHA2_384

(** @type: true
*)
val compute_sha2_512: compute_st SHA2_512


let is_supported_alg = function
| SHA1 | SHA2_256 | SHA2_384 | SHA2_512 -> true
| _ -> false

let supported_alg = a:hash_alg{ is_supported_alg a }

/// The agile version that dynamically dispatches between the above four

//18-07-13 pick uniform names? hash{spec} vs compute{hmac}

(* The implementation of compute relies on 3 the variants of SHA2 supported by HACL*;
   Tolerates overlaps between tag and data (we used to require [disjoint data tag])
*)

(** @type: true
*)
val compute: a: supported_alg -> compute_st a
