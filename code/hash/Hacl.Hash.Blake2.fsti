module Hacl.Hash.Blake2

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

// Blake2B_32

inline_for_extraction noextract
val malloc_blake2b_32: malloc_st (|Blake2B, M32|)

inline_for_extraction noextract
val alloca_blake2b_32: alloca_st (|Blake2B, M32|)

inline_for_extraction noextract
val init_blake2b_32: init_st (|Blake2B, M32|)

inline_for_extraction noextract
val update_multi_blake2b_32: update_multi_st (|Blake2B, M32|)

inline_for_extraction noextract
val update_last_blake2b_32: update_last_st (|Blake2B, M32|)

inline_for_extraction noextract
val finish_blake2b_32: finish_st (|Blake2B, M32|)

inline_for_extraction noextract
val hash_blake2b_32: hash_st Blake2B

// Blake2S_32

inline_for_extraction noextract
val malloc_blake2s_32: malloc_st (|Blake2S, M32|)

inline_for_extraction noextract
val alloca_blake2s_32: alloca_st (|Blake2S, M32|)

inline_for_extraction noextract
val init_blake2s_32: init_st (|Blake2S, M32|)

inline_for_extraction noextract
val update_multi_blake2s_32: update_multi_st (|Blake2S, M32|)

inline_for_extraction noextract
val update_last_blake2s_32: update_last_st (|Blake2S, M32|)

inline_for_extraction noextract
val finish_blake2s_32: finish_st (|Blake2S, M32|)

inline_for_extraction noextract
val hash_blake2s_32: hash_st Blake2S

// As mentioned above, this module generates no code at run-time, so we can
// safely put vectorized versions in a file that does not contain a _128 or _256
// suffix: these combinators will be inlined in their respective files, e.g.
// Hacl_HMAC_Blake2s_128.c

// Blake2S_128

inline_for_extraction noextract
val malloc_blake2s_128: malloc_st (|Blake2S, M128|)

inline_for_extraction noextract
val alloca_blake2s_128: alloca_st (|Blake2S, M128|)

inline_for_extraction noextract
val init_blake2s_128: init_st (|Blake2S, M128|)

inline_for_extraction noextract
val update_multi_blake2s_128: update_multi_st (|Blake2S, M128|)

inline_for_extraction noextract
val update_last_blake2s_128: update_last_st (|Blake2S, M128|)

inline_for_extraction noextract
val finish_blake2s_128: finish_st (|Blake2S, M128|)

inline_for_extraction noextract
val hash_blake2s_128: hash_st Blake2S

// Blake2B_256

inline_for_extraction noextract
val malloc_blake2b_256: malloc_st (|Blake2B, M256|)

inline_for_extraction noextract
val alloca_blake2b_256: alloca_st (|Blake2B, M256|)

inline_for_extraction noextract
val init_blake2b_256: init_st (|Blake2B, M256|)

inline_for_extraction noextract
val update_multi_blake2b_256: update_multi_st (|Blake2B, M256|)

inline_for_extraction noextract
val update_last_blake2b_256: update_last_st (|Blake2B, M256|)

inline_for_extraction noextract
val finish_blake2b_256: finish_st (|Blake2B, M256|)

inline_for_extraction noextract
val hash_blake2b_256: hash_st Blake2B
