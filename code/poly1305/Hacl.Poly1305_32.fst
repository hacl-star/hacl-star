module Hacl.Poly1305_32

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305


let blocklen = 16ul

type poly1305_ctx = lbuffer (Lib.IntVector.vec_t U64 1) 25ul

let poly1305_init: poly1305_init_st M32 = poly1305_init #M32

[@CInline]
let poly1305_update: poly1305_update_st M32 = poly1305_update #M32

let poly1305_finish: poly1305_finish_st M32 =
  poly1305_finish #M32

let poly1305_mac: poly1305_mac_st M32 =
  mk_poly1305_mac #M32 poly1305_init poly1305_update poly1305_finish
