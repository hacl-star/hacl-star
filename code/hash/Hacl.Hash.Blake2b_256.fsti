module Hacl.Hash.Blake2b_256

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
val malloc: malloc_st (|Blake2B, M256|)

inline_for_extraction noextract
val alloca: alloca_st (|Blake2B, M256|)

inline_for_extraction noextract
val init: init_st (|Blake2B, M256|)

inline_for_extraction noextract
val update_multi: update_multi_st (|Blake2B, M256|)

inline_for_extraction noextract
val update_last: update_last_st (|Blake2B, M256|)

inline_for_extraction noextract
val finish: finish_st (|Blake2B, M256|)

inline_for_extraction noextract
val hash: hash_st Blake2B

module B = LowStar.Buffer
open FStar.HyperStack.ST

val copy (src dst: state (| Spec.Agile.Hash.Blake2B, Hacl.Impl.Blake2.Core.M256 |)): Stack unit
  (requires (fun h0 -> B.(live h0 src /\ live h0 dst /\ loc_disjoint (loc_buffer src) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1 /\ as_seq h1 dst `Seq.equal` as_seq h0 src)))
