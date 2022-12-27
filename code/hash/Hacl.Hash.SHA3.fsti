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
// Final remark: this module is completely noextract, so it generates no code at run-time.

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

inline_for_extraction noextract
val init_256: init_st (|SHA3_256, ()|)

inline_for_extraction noextract
val update_multi_256: update_multi_st (|SHA3_256, ()|)

inline_for_extraction noextract
val update_last_256: update_last_st (|SHA3_256, ()|)

inline_for_extraction noextract
val finish_256: finish_st (|SHA3_256, ()|)

inline_for_extraction noextract
val hash_256: hash_st SHA3_256
