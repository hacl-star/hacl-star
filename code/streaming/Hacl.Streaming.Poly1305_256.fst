module Hacl.Streaming.Poly1305_256

module G = FStar.Ghost
module F = Hacl.Streaming.Functor
module Stateful = Hacl.Streaming.Stateful

open Hacl.Impl.Poly1305.Fields
open Hacl.Streaming.Poly1305

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

/// Type abbreviation - makes KaRaMeL use pretty names in the generated code
let poly1305_256_state = F.state_s (poly1305_index M256) (t M256) (poly1305_key.Stateful.s)

noextract
let alloca : F.alloca_st (poly1305_index M256) = mk_alloca M256
let create_in : F.create_in_st (poly1305_index M256) = mk_create_in M256
let init : F.init_st (poly1305_index M256) = mk_init M256
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update : F.update_st (poly1305_index M256) = mk_update M256
let finish : F.finish_st (poly1305_index M256) = mk_finish M256
let free : F.free_st (poly1305_index M256) = mk_free M256
