module Hacl.Streaming.Poly1305_128

module G = FStar.Ghost
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface

open Hacl.Impl.Poly1305.Fields
open Hacl.Streaming.Poly1305

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

/// Type abbreviation - makes KaRaMeL use pretty names in the generated code
let state_t = F.state_s (poly1305 M128) () (t M128) (k.I.s ())

noextract
let alloca = F.alloca (poly1305 M128) () (t M128) (k.I.s ())
let malloc = F.malloc (poly1305 M128) () (t M128) (k.I.s ())
let reset = F.reset (poly1305 M128) (G.hide ()) (t M128) (k.I.s ())
[@@ Comment "0 = success, 1 = max length exceeded" ]
let update = F.update (poly1305 M128) (G.hide ()) (t M128) (k.I.s ())
let digest = F.digest (poly1305 M128) () (t M128) (k.I.s ())
let free = F.free (poly1305 M128) (G.hide ()) (t M128) (k.I.s ())
