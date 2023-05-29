module Hacl.Hash.SHA3

// This module contains low-level implementations that implement the
// "incremental" API, found in Spec.Hash.Incremental.
//
// This is just a lightweight wrapper around the actual implementation in
// code/sha3; by re-exporting the correct type signatures, this makes
// instantiating the streaming functor trivial. (Also note that the
// implementation in code/sha3 does not export the "update_multi" version, since
// it does everything in one go, so it's convenient to make this explicit here.)
//
// NOTE: unlike other modules, this one is not entirely noextract
// inline_for_extraction. There are two reasons. First, because all Keccak
// variants share the same state type, these functions do *NOT* need to be
// inlined to fit in the Low* subset. Second, for this reason, they are not
// always reduced at compile-time for a chosen value of `a`, meaning that we
// need the code to look decent (and not have everything inlined aggressively
// when there are no opportunities for reduction).

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

val block_len (a: keccak_alg): Lib.IntTypes.(n:size_t { v n = block_length a })
val hash_len (a: keccak_alg { not (is_shake a) }): Lib.IntTypes.(n:size_t { v n = hash_length a })

inline_for_extraction noextract
val init (a: keccak_alg): init_st (|a, ()|)

inline_for_extraction noextract
val update_multi (a: keccak_alg): update_multi_st (|a, ()|)

inline_for_extraction noextract
val update_last (a: keccak_alg): update_last_st (|a, ()|)

inline_for_extraction noextract
val finish (a: keccak_alg { not (is_shake a) }): finish_st (| a, ()|)

inline_for_extraction noextract
val hash (a: keccak_alg { not (is_shake a) }): hash_st a

/// A couple helpers specifically for the Keccak functor, which live here
/// because this module has an fsti and therefore can friend specs.

let v_len a (l: Lib.IntTypes.size_t): Spec.Hash.Definitions.output_length a =
  let _ = allow_inversion hash_alg in
  if is_shake a then
    Lib.IntTypes.(v #U32 #PUB (l <: size_t))
  else
    ()

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST

/// This is a variant of Hacl.Hash.SHA3.finish that takes an optional output
/// length. This is used in the Keccak streaming functor, wherein this signature
/// eventually becomes exposed in the C API. As a result, we cannot have `l` be
/// an indexed type (e.g. if is_shake then size_t else unit) because that would
/// not be extractable to C. So, we contend with a suboptimal contract, which
/// is: "unless a is a shake algorithm, the length is ignored".
noextract inline_for_extraction
let finish_st (a: keccak_alg) =
  s:state (| a, () |) -> dst:B.buffer Lib.IntTypes.uint8 -> l:Lib.IntTypes.size_t {
    B.length dst == (if is_shake a then Lib.IntTypes.(v (l <: size_t))  else Spec.Hash.Definitions.hash_length a)
  } -> ST.Stack unit
  (requires (fun h ->
    B.live h s /\ B.live h dst /\ B.disjoint s dst))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer dst `loc_union` loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Agile.Hash.finish a (as_seq h0 s) (v_len a l))))

noextract inline_for_extraction
val finish_keccak (a: keccak_alg): finish_st a
