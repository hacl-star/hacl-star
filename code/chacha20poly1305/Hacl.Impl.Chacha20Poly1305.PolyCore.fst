module Hacl.Impl.Chacha20Poly1305.PolyCore

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20Poly1305
module Poly = Hacl.Impl.Poly1305


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1 --record_options"

inline_for_extraction noextract
let poly1305_padded_st (w:field_spec) =
    ctx:Poly.poly1305_ctx w
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ disjoint ctx text /\
    Poly.state_inv_t h ctx)
  (ensures fun h0 _ h1 ->
    modifies (loc ctx) h0 h1 /\
    Poly.state_inv_t h1 ctx /\
    Poly.as_get_r h0 ctx == Poly.as_get_r h1 ctx /\
    Poly.as_get_acc h1 ctx ==
      Spec.poly1305_padded (Poly.as_get_r h0 ctx) (as_seq h0 text) (Poly.as_get_acc h0 ctx))


inline_for_extraction noextract
val poly1305_padded: #w:field_spec -> poly1305_padded_st w
[@Meta.Attribute.specialize]
let poly1305_padded #w ctx len text =
  let h0 = ST.get () in
  push_frame ();
  let h1 = ST.get () in
  Poly.reveal_ctx_inv ctx h0 h1;
  let n = len /. 16ul in
  let r = len %. 16ul in
  let blocks = sub text 0ul (n *! 16ul) in
  let rem = sub text (n *! 16ul) r in // the extra part of the input data
  Poly.poly1305_update #w ctx (n *! 16ul) blocks;
  let h2 = ST.get () in
  let tmp = create 16ul (u8 0) in
  update_sub tmp 0ul r rem;
  let h3 = ST.get() in
  Poly.reveal_ctx_inv ctx h2 h3;
  if r >. 0ul then
    Poly.poly1305_update1 ctx tmp;
  let h4 = ST.get () in
  pop_frame();
  let h5 = ST.get () in
  Poly.reveal_ctx_inv ctx h4 h5
