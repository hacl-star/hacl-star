(** Agile HMAC *)
module EverCrypt.HMAC

/// 18-03-03 Do we get specialized extraction of HMAC?

open Spec.HMAC
open EverCrypt.Hash
open Spec.Hash.Definitions

open FStar.HyperStack.ST
open LowStar.Buffer

#reset-options "--max_fuel 0  --z3rlimit 20"
(* implementation, relying on 3 variants of SHA2 supported by HACL*;
   we tolerate overlaps between tag and data.
   (we used to require [disjoint data tag])
*)

open EverCrypt.Helpers

inline_for_extraction
let compute_st (a: hash_alg) =
  tag: uint8_pl (hash_length a) ->
  key: uint8_p{ keysized a (length key) /\ disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = length key } ->
  data: uint8_p{ length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = length data } ->
  Stack unit
  (requires fun h0 -> live h0 tag /\ live h0 key /\ live h0 data)
  (ensures fun h0 _ h1 ->
    live h1 tag /\
    live h1 key /\
    live h1 data /\
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    length data + block_length a < max_input_length a /\ (* required for subtyping the RHS below *)
    as_seq h1 tag == hmac a (as_seq h0 key) (as_seq h0 data))

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
