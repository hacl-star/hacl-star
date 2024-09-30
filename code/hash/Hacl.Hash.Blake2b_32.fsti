module Hacl.Hash.Blake2b_32

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
val malloc: malloc_st (|Blake2B, M32|)

inline_for_extraction noextract
val alloca: alloca_st (|Blake2B, M32|)

inline_for_extraction noextract
val init: init_st (|Blake2B, M32|)

inline_for_extraction noextract
val update_multi: update_multi_st (|Blake2B, M32|)

inline_for_extraction noextract
val update_last: update_last_st (|Blake2B, M32|)

inline_for_extraction noextract
val finish: finish_st (|Blake2B, M32|)

inline_for_extraction noextract
val hash: hash_st Blake2B
