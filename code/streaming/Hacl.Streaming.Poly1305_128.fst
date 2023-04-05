module Hacl.Streaming.Poly1305_128

open Hacl.Meta.Poly1305
open Hacl.Poly1305_128

friend Hacl.Meta.Poly1305

(* The one-shot MAC *)
let mac = poly1305_poly1305_mac_higher #M128 True poly1305_finish poly1305_update poly1305_init
