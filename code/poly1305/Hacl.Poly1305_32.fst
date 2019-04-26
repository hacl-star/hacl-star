module Hacl.Poly1305_32

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Impl.Poly1305
module S = Hacl.Spec.Poly1305.Vec

let blocklen = 16ul

type poly1305_ctx = lbuffer (Lib.IntVector.vec_t U64 1) 25ul

let poly1305_init: poly1305_init_st M32 = poly1305_init #M32

[@ CInline]
let poly1305_update: poly1305_update_st M32 = poly1305_update #M32

val poly1305_update_blocks:
    ctx:poly1305_ctx
  -> len:size_t{v len % v blocklen == 0}
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #M32 h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #M32 h1 ctx /\
      as_get_acc h1 ctx ==
      S.poly_update #(width M32) (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update_blocks ctx len text =
  poly1305_update ctx len text

let poly1305_update_padded: poly1305_update_st M32 =
  poly1305_update

val poly1305_update_last:
    ctx:poly1305_ctx
  -> len:size_t{v len < 16}
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #M32 h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #M32 h1 ctx /\
      as_get_acc h1 ctx ==
      S.poly_update #(width M32) (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update_last ctx len text =
  poly1305_update ctx len text

let poly1305_finish: poly1305_finish_st M32 =
  poly1305_finish #M32

let poly1305_mac: poly1305_mac_st M32 =
  mk_poly1305_mac #M32 poly1305_init poly1305_update_padded poly1305_finish
