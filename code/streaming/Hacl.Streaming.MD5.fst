module Hacl.Streaming.MD5

/// WARNING: this file is here for legacy purposes only. You SHOULD NOT use
/// it in new code.

open FStar.HyperStack.ST

/// A streaming version of MD-based hashes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Interface
open Hacl.Streaming.MD

/// Instantiations of the streaming functor for MD5
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_md5 = hacl_md MD5

inline_for_extraction noextract
let state_t_md5 = state_t MD5

/// Type abbreviation - for pretty code generation
let state_t = Hacl.Streaming.MD.state_32

noextract
let legacy_alloca = F.alloca hacl_md5 () (state_t_md5.s ()) (G.erased unit)
let legacy_malloc = F.malloc hacl_md5 () (state_t_md5.s ()) (G.erased unit)
let legacy_reset = F.reset hacl_md5 (G.hide ()) (state_t_md5.s ()) (G.erased unit)

[@@ Comment "0 = success, 1 = max length exceeded" ]
let legacy_update = F.update hacl_md5 (G.hide ()) (state_t_md5.s ()) (G.erased unit)
let legacy_digest = F.digest hacl_md5 () (state_t_md5.s ()) (G.erased unit)
let legacy_free = F.free hacl_md5 (G.hide ()) (state_t_md5.s ()) (G.erased unit)

let legacy_copy = F.copy hacl_md5 () (state_t_md5.s ()) (G.erased unit)

let legacy_hash: Hacl.Hash.Definitions.hash_st MD5 = fun output input input_len -> Hacl.Hash.MD5.legacy_hash output input input_len
