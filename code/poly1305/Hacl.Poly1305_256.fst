module Hacl.Poly1305_256

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305


let blocklen = 16ul

type poly1305_ctx = lbuffer (Lib.IntVector.vec_t U64 4) 25ul

let poly1305_init: poly1305_init_st M256 = poly1305_init #M256

[@ CInline]
let poly1305_update: poly1305_update_st M256 = poly1305_update #M256

let poly1305_finish: poly1305_finish_st M256 =
  poly1305_finish #M256

let poly1305_mac: poly1305_mac_st M256 =
  mk_poly1305_mac #M256 poly1305_init poly1305_update poly1305_finish
