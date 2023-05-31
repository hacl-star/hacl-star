module Hacl.Streaming.Poly1305_32

module G = FStar.Ghost
module F = Hacl.Streaming.Functor
module Stateful = Hacl.Streaming.Stateful

open Hacl.Impl.Poly1305.Fields
open Hacl.Streaming.Poly1305

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

/// Type abbreviation - makes KaRaMeL use pretty names in the generated code
let poly1305_32_state = F.state_s (poly1305_index M32) (t M32) (poly1305_key.Stateful.s)

noextract
let alloca : F.alloca_st (poly1305_index M32) = mk_alloca M32
let create_in : F.create_in_st (poly1305_index M32) = mk_create_in M32
let init : F.init_st (poly1305_index M32) = mk_init M32
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update : F.update_st (poly1305_index M32) = mk_update M32
let finish : F.finish_st (poly1305_index M32) = mk_finish M32
let free : F.free_st (poly1305_index M32) = mk_free M32
