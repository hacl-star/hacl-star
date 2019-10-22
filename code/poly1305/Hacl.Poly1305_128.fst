module Hacl.Poly1305_128

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305
open Hacl.Meta.Poly1305

friend Hacl.Meta.Poly1305

let poly1305_init = poly1305_init #M128

let poly1305_update1 = poly1305_update1 #M128

let poly1305_update = poly1305_update #M128

let poly1305_finish = poly1305_finish #M128

let poly1305_mac = poly1305_poly1305_mac_higher #M128 poly1305_finish poly1305_update poly1305_init
