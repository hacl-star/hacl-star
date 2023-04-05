module Hacl.Streaming.Poly1305_256

open Hacl.Meta.Poly1305
open Hacl.Poly1305_256

friend Hacl.Meta.Poly1305

(* The one-shot MAC *)
let mac = poly1305_poly1305_mac_higher #M256 True poly1305_finish poly1305_update poly1305_init
