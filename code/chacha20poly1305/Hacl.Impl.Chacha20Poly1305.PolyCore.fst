module Hacl.Impl.Chacha20Poly1305.PolyCore

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Spec.Poly1305.Equiv

module SpecPolyVec = Hacl.Spec.Poly1305.Vec
module SpecPoly = Spec.Poly1305
module Spec = Spec.Chacha20Poly1305
module Poly = Hacl.Impl.Poly1305

inline_for_extraction noextract
let poly1305_padded_st (w:field_spec) =
    ctx:Poly.poly1305_ctx w
  -> len:size_t
  -> text:lbuffer uint8 len
  -> tmp:lbuffer uint8 16ul ->
  Stack unit
    (requires fun h ->
      live h ctx /\ live h text /\ live h tmp /\
      disjoint ctx text /\ disjoint ctx tmp /\ disjoint text tmp /\
      Poly.state_inv_t h ctx)
    (ensures fun h0 _ h1 ->
      modifies (loc tmp |+| loc ctx) h0 h1 /\
      Poly.state_inv_t h1 ctx /\
      // Additional framing for r_elem
      Poly.as_get_r h0 ctx == Poly.as_get_r h1 ctx /\
      // Functional spec
      Poly.as_get_acc h1 ctx ==
      Spec.poly1305_padded
        (Poly.as_get_r h0 ctx)
        (v len)
        (as_seq h0 text)
        (as_seq h0 tmp)
        (Poly.as_get_acc h0 ctx))

inline_for_extraction noextract
val poly1305_padded_: #w:field_spec -> poly1305_padded_st w
let poly1305_padded_ #w ctx len text tmp =
  let n = len /. 16ul in
  let r = len %. 16ul in
  let blocks = sub text 0ul (n *! 16ul) in
  let rem = sub text (n *! 16ul) r in // the extra part of the input data
  let h0 = ST.get() in
  Poly.poly1305_update #w ctx (n *! 16ul) blocks;
  let h1 = ST.get() in
  poly_eq_lemma #(width w) (as_seq h0 blocks) (Poly.as_get_acc h0 ctx) (Poly.as_get_r h0 ctx);
  update_sub tmp 0ul r rem;
  let h2 = ST.get() in
  Poly.reveal_ctx_inv ctx h1 h2;
  if r >. 0ul then
    Poly.poly1305_update1 ctx tmp

[@CInline]
let poly1305_padded_32 : poly1305_padded_st M32 = poly1305_padded_
[@CInline]
let poly1305_padded_128 : poly1305_padded_st M128 = poly1305_padded_
[@CInline]
let poly1305_padded_256 : poly1305_padded_st M256 = poly1305_padded_

inline_for_extraction noextract
val poly1305_padded: #w:field_spec -> poly1305_padded_st w
let poly1305_padded #w =
  match w with
  | M32 -> poly1305_padded_32
  | M128 -> poly1305_padded_128
  | M256 -> poly1305_padded_256
