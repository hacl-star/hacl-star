(** Agile HMAC *)
module EverCrypt.HMAC

module B = LowStar.Buffer

open Spec.HMAC
open Spec.Hash.Definitions

open FStar.HyperStack.ST

#reset-options "--max_fuel 0  --z3rlimit 20"
(* implementation, relying on 3 variants of SHA2 supported by HACL*;
   we tolerate overlaps between tag and data.
   (we used to require [disjoint data tag])
*)

open EverCrypt.Helpers

inline_for_extraction
let compute_st (a: hash_alg) =
  tag: B.buffer Lib.IntTypes.uint8 {B.length tag == hash_length a} ->
  key: B.buffer Lib.IntTypes.uint8{ keysized a (B.length key) /\ B.disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = B.length key } ->
  data: B.buffer Lib.IntTypes.uint8{ B.length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = B.length data } ->
  Stack unit
  (requires fun h0 -> B.live h0 tag /\ B.live h0 key /\ B.live h0 data)
  (ensures fun h0 _ h1 ->
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\ (
    assert_norm (pow2 32 < pow2 61 - 1);
    assert_norm (pow2 32 < pow2 125 - 1);
    B.as_seq h1 tag == hmac a (B.as_seq h0 key) (B.as_seq h0 data)))

// Four monomorphized variants, for callers who already know which algorithm they want.
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

let supported_alg = a:hash_alg { is_supported_alg a }

// The agile version that dynamically dispatches between the above four.
(** @type: true
*)
val compute: a: supported_alg -> compute_st a

//18-07-13 pick uniform names? hash{spec} vs compute{hmac}
