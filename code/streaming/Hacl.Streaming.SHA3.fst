module Hacl.Streaming.SHA3

open FStar.HyperStack.ST

/// An instantiation of the streaming functor for just SHA3.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Interface
open Hacl.Streaming.MD

inline_for_extraction noextract
let hacl_sha3_256 = hacl_md SHA3_256

inline_for_extraction noextract
let state_t_256 = state_t SHA3_256

/// Type abbreviations - for pretty code generation
let state_sha3_256 = F.state_s hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)

inline_for_extraction noextract
let alloca_256 = F.alloca hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let create_in_256 = F.create_in hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let init_256 = F.init hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let update_256 = F.update hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let finish_256 = F.mk_finish hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let free_256 = F.free hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
