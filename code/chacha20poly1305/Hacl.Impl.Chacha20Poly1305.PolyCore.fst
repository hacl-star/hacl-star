module Hacl.Impl.Chacha20Poly1305.PolyCore

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Fields
open Hacl.Spec.Poly1305.Equiv

module SpecPoly = Spec.Poly1305
module Spec = Spec.Chacha20Poly1305
module Poly = Hacl.Impl.Poly1305

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let poly1305_padded ctx len text tmp =
  let h_init = ST.get() in
  let n = len /. 16ul in
  //div_lemma len 16ul;
  let r = len %. 16ul in
  //mod_lemma len 16ul;
  let blocks = sub text 0ul (n *. 16ul) in
  //mul_lemma n 16ul;
  let rem = sub text (n *. 16ul) r in // the extra part of the input data
  let h0 = ST.get() in
  poly_eq_lemma_vec #1 (as_seq h0 blocks) (Poly.as_get_acc h0 ctx) (Poly.as_get_r h0 ctx);
  Poly.poly1305_update ctx (n *. 16ul) blocks;
  let h1 = ST.get() in
  update_sub tmp 0ul r rem;
  let h2 = ST.get() in
  Poly.reveal_ctx_inv ctx h1 h2;
  poly_update1_is_update1 (Poly.as_get_r h2 ctx) 16 (as_seq h2 tmp) (Poly.as_get_acc h2 ctx);
  Poly.poly1305_update ctx 16ul tmp

let poly1305_init ctx k = Poly.poly1305_init ctx k

let update1 ctx len text =
  let h0 = ST.get() in
  poly_update1_is_update1 (Poly.as_get_r h0 ctx) (v len) (as_seq h0 text) (Poly.as_get_acc h0 ctx);
  Poly.poly1305_update ctx len text

let finish ctx k out = Poly.poly1305_finish out k ctx
