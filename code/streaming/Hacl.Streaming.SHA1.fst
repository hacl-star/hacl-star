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

/// Type abbreviation - for pretty code generation
let state_t = Hacl.Streaming.MD.state_32

noextract
let alloca = F.alloca hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let malloc = F.malloc hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let reset = F.reset hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update = F.update hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)
let digest = F.digest hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)
let free = F.free hacl_sha1 (G.hide ()) (state_t_sha1.s ()) (G.erased unit)

let copy = F.copy hacl_sha1 () (state_t_sha1.s ()) (G.erased unit)

let hash: Hacl.Hash.Definitions.hash_st SHA1 = fun output input input_len -> Hacl.Hash.SHA1.legacy_hash output input input_len
