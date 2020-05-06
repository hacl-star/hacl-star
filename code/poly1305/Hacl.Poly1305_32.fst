module Hacl.Poly1305_32

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305
open Hacl.Meta.Poly1305

friend Hacl.Meta.Poly1305

let poly1305_init = poly1305_init #M32

let poly1305_update1 = poly1305_update1 #M32

let poly1305_update = poly1305_update #M32

let poly1305_finish = poly1305_finish #M32

let poly1305_mac = poly1305_poly1305_mac_higher #M32 True poly1305_finish poly1305_update poly1305_init
