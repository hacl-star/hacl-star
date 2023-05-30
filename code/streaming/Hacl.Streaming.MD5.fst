module Hacl.Streaming.MD5

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

/// Instantiations of the streaming functor for MD5
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_md5 = hacl_md_index MD5

inline_for_extraction noextract
let state_t_md5 = state_t MD5

/// Type abbreviation - for pretty code generation
let state = Hacl.Streaming.MD.state_32

noextract
let legacy_alloca : F.alloca_st hacl_md5 = mk_alloca MD5
let legacy_create_in : F.create_in_st hacl_md5 = mk_create_in MD5
let legacy_init : F.init_st hacl_md5 = mk_init MD5

[@@ Comment "0 = success, 1 = max length exceeded" ]
let legacy_update : F.update_st hacl_md5 = mk_update MD5

let legacy_finish : F.finish_st hacl_md5 = mk_finish MD5
let legacy_free : F.free_st hacl_md5 = mk_free MD5
let legacy_copy : F.copy_st hacl_md5 = mk_copy MD5
let legacy_hash: Hacl.Hash.Definitions.hash_st MD5 =
  fun input input_len dst -> Hacl.Hash.MD5.legacy_hash input input_len dst
