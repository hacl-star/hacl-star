module Hacl.Poly1305_32
open Hacl.Impl.Poly1305.Fields
open Lib.IntTypes

let poly1305_mac o t l k = Hacl.Impl.Poly1305.poly1305_mac #M32 o t l k
