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

unfold
let op_String_Access #a #len = Lib.Sequence.index #a #len

val poly1305_init:
    ctx:poly1305_ctx
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h ctx /\ live h key /\ disjoint ctx key)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #M32 h1 ctx /\
      (as_get_acc h1 ctx, as_get_r h1 ctx) == S.poly1305_init (as_seq h0 key))
let poly1305_init ctx key =
  poly1305_init #M32 ctx key

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
      (as_get_acc h1 ctx).[0] ==
      S.poly_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update_blocks ctx len text =
  poly1305_update #M32 ctx len text

val poly1305_update_padded:
    ctx:poly1305_ctx
  -> len:size_t
  -> text:lbuffer uint8 len
  -> Stack unit
    (requires fun h ->
      live h text /\ live h ctx /\ disjoint ctx text /\
      state_inv_t #M32 h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc ctx) h0 h1 /\
      state_inv_t #M32 h1 ctx /\
      (as_get_acc h1 ctx).[0] ==
      S.poly_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update_padded ctx len text =
  poly1305_update #M32 ctx len text

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
      (as_get_acc h1 ctx).[0] ==
      S.poly_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))
let poly1305_update_last ctx len text =
  poly1305_update #M32 ctx len text

val poly1305_finish:
    tag:lbuffer uint8 16ul
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx
  -> Stack unit
    (requires fun h ->
      live h tag /\ live h key /\ live h ctx /\
      disjoint tag key /\ disjoint tag ctx /\ disjoint key ctx /\
      state_inv_t h ctx)
    (ensures  fun h0 _ h1 ->
      modifies (loc tag |+| loc ctx) h0 h1 /\
      as_seq h1 tag == S.finish (as_seq h0 key) (as_get_acc h0 ctx).[0])
let poly1305_finish tag k ctx =
  poly1305_finish #M32 tag k ctx

val poly1305_mac:
    o:lbuffer uint8 16ul
  -> text:buffer uint8
  -> len:size_t{length text == v len}
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h text /\ live h o /\ live h key /\
      disjoint o text /\ disjoint o key)
    (ensures  fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      as_seq h1 o == S.poly1305 #1 (as_seq #MUT #uint8 #len h0 text) (as_seq h0 key))
let poly1305_mac o t l k =
  poly1305_mac #M32 o l t k
