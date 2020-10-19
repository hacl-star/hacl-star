module Hacl.Streaming.SHA1

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

/// Instantiations of the streaming functor for SHA1
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_sha1 = hacl_md SHA1

inline_for_extraction noextract
let state_t_sha1 = state_t SHA1

noextract
let legacy_alloca_sha1 = F.alloca hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let legacy_create_in_sha1 = F.create_in hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let legacy_init_sha1 = F.init hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)
let legacy_update_sha1 = F.update hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)
let legacy_finish_sha1 = F.mk_finish hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let legacy_free_sha1 = F.free hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)
