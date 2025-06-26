module Hacl.Hash.Blake2s_128

// This module contains low-level implementations that implement the
// "update_multi" API, found in Spec.Agile.Hash.
//
// This is just a lightweight wrapper around the actual implementation in
// code/blake2; by re-exporting the correct type signatures, this makes
// instantiating the HMAC implementation trivial (which is defined in terms of
// update_multi).
//
// Final remark: this module is completely noextract, so it generates no code at run-time.

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Impl.Blake2.Core

inline_for_extraction noextract
val malloc: malloc_st (|Blake2S, M128|)

inline_for_extraction noextract
val alloca: alloca_st (|Blake2S, M128|)

inline_for_extraction noextract
val init: init_st (|Blake2S, M128|)

inline_for_extraction noextract
val update_multi: update_multi_st (|Blake2S, M128|)

let update_multi_no_inline: update_multi_st (|Blake2S, M128|) = update_multi

inline_for_extraction noextract
val update_last: update_last_st (|Blake2S, M128|)

let update_last_no_inline: update_last_st (|Blake2S, M128|) = update_last

inline_for_extraction noextract
val finish: finish_st (|Blake2S, M128|)

inline_for_extraction noextract
val hash: hash_st Blake2S

module B = LowStar.Buffer
open FStar.HyperStack.ST

val copy_internal_state (src dst: state (| Spec.Agile.Hash.Blake2S, Hacl.Impl.Blake2.Core.M128 |)): Stack unit
  (requires (fun h0 -> B.(live h0 src /\ live h0 dst /\ loc_disjoint (loc_buffer src) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1 /\ as_seq h1 dst `Seq.equal` as_seq h0 src)))
