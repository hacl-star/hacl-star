module Hacl.Streaming.SHA2

open FStar.HyperStack.ST

/// A streaming version of MD-based hashes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Interface
open Hacl.Streaming.MD

/// Instantiations of the streaming functor for specialized SHA2 algorithms.
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_sha2_224 = hacl_md SHA2_224
inline_for_extraction noextract
let hacl_sha2_256 = hacl_md SHA2_256
inline_for_extraction noextract
let hacl_sha2_384 = hacl_md SHA2_384
inline_for_extraction noextract
let hacl_sha2_512 = hacl_md SHA2_512

inline_for_extraction noextract
let state_t_224 = state_t SHA2_224
inline_for_extraction noextract
let state_t_256 = state_t SHA2_256
inline_for_extraction noextract
let state_t_384 = state_t SHA2_384
inline_for_extraction noextract
let state_t_512 = state_t SHA2_512

/// Type abbreviations - for pretty code generation
let state_sha2_224 = F.state_s hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let state_sha2_256 = F.state_s hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let state_sha2_384 = F.state_s hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let state_sha2_512 = F.state_s hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)

inline_for_extraction noextract
let alloca_224 = F.alloca hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let create_in_224 = F.create_in hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let init_224 = F.init hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
let update_224 = F.update hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)
let finish_224 = F.mk_finish hacl_sha2_224 () (state_t_224.s ()) (G.erased unit)
let free_224 = F.free hacl_sha2_224 (G.hide ()) (state_t_224.s ()) (G.erased unit)

inline_for_extraction noextract
let alloca_256 = F.alloca hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let create_in_256 = F.create_in hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let init_256 = F.init hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let update_256 = F.update hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let finish_256 = F.mk_finish hacl_sha2_256 () (state_t_256.s ()) (G.erased unit)
let free_256 = F.free hacl_sha2_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)

inline_for_extraction noextract
let alloca_384 = F.alloca hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let create_in_384 = F.create_in hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let init_384 = F.init hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
let update_384 = F.update hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)
let finish_384 = F.mk_finish hacl_sha2_384 () (state_t_384.s ()) (G.erased unit)
let free_384 = F.free hacl_sha2_384 (G.hide ()) (state_t_384.s ()) (G.erased unit)

inline_for_extraction noextract
let alloca_512 = F.alloca hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let create_in_512 = F.create_in hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let init_512 = F.init hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
let update_512 = F.update hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
let finish_512 = F.mk_finish hacl_sha2_512 () (state_t_512.s ()) (G.erased unit)
let free_512 = F.free hacl_sha2_512 (G.hide ()) (state_t_512.s ()) (G.erased unit)
