module Hacl.Poly1305_512

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305
open Hacl.Meta.Poly1305

friend Hacl.Meta.Poly1305

let poly1305_init = poly1305_init #M512

let poly1305_update1 = poly1305_update1 #M512

let poly1305_update = poly1305_update #M512

let poly1305_finish = poly1305_finish #M512

let poly1305_mac = poly1305_poly1305_mac_higher #M512 True poly1305_finish poly1305_update poly1305_init
