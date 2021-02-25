module Hacl.Streaming.Poly1305_32

module G = FStar.Ghost
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface

open Hacl.Impl.Poly1305.Fields
open Hacl.Streaming.Poly1305

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

/// Type abbreviation - makes Kremlin use pretty names in the generated code
let poly1305_32_state = F.state_s (poly1305 M32) () (t M32) (k.I.s ())

noextract
let alloca = F.alloca (poly1305 M32) () (t M32) (k.I.s ())
let create_in = F.create_in (poly1305 M32) () (t M32) (k.I.s ())
let init = F.init (poly1305 M32) (G.hide ()) (t M32) (k.I.s ())
let update = F.update (poly1305 M32) (G.hide ()) (t M32) (k.I.s ())
let finish = F.mk_finish (poly1305 M32) () (t M32) (k.I.s ())
let free = F.free (poly1305 M32) (G.hide ()) (t M32) (k.I.s ())
