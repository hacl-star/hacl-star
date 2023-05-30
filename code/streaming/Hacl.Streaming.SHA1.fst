module Hacl.Streaming.SHA1

/// WARNING: this file is here for legacy purposes only. You SHOULD NOT use
/// it in new code.

open FStar.HyperStack.ST

/// A streaming version of MD-based hashes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Block
open Hacl.Streaming.MD

/// Instantiations of the streaming functor for SHA1
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_sha1 = hacl_md_index SHA1

inline_for_extraction noextract
let state_t_sha1 = state_t SHA1

/// Type abbreviation - for pretty code generation
let state = Hacl.Streaming.MD.state_32

noextract
let legacy_alloca : F.alloca_st hacl_sha1 = mk_alloca SHA1
let legacy_create_in : F.create_in_st hacl_sha1 = mk_create_in SHA1
let legacy_init : F.init_st hacl_sha1 = mk_init SHA1

[@@ Comment "0 = success, 1 = max length exceeded" ]
let legacy_update : F.update_st hacl_sha1 = mk_update SHA1

let legacy_finish : F.finish_st hacl_sha1 = mk_finish SHA1
let legacy_free : F.free_st hacl_sha1 = mk_free SHA1
let legacy_copy : F.copy_st hacl_sha1 = mk_copy SHA1

let legacy_hash: Hacl.Hash.Definitions.hash_st SHA1 =
  fun input input_len dst -> Hacl.Hash.SHA1.legacy_hash input input_len dst
