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
let state_256 = Hacl.Streaming.MD.state_64

inline_for_extraction noextract
let alloca_256 = F.alloca hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let malloc_256 = F.malloc hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let reset_256 = F.reset hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
[@@ Comment "0 = success, 1 = max length exceeded. Due to internal limitations, there is currently an arbitrary limit of 2^64-1 bytes that can be hashed through this interface." ]
let update_256 = F.update hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let digest_256 = F.digest hacl_sha3_256 () (state_t_256.s ()) (G.erased unit)
let free_256 = F.free hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
let copy_256 = F.copy hacl_sha3_256 (G.hide ()) (state_t_256.s ()) (G.erased unit)
