module Hacl.Impl.Chacha20Poly1305.PolyLemmas

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.ByteSequence
module Seq = Lib.Sequence
open FStar.Mul

module SpecPoly = Spec.Poly1305
module Spec = Spec.Chacha20Poly1305
module Poly = Hacl.Impl.Poly1305
open Hacl.Impl.Poly1305.Fields

val same_ctx_same_r_acc:
  ctx:Poly.poly1305_ctx M32 ->
  h0:mem ->
  h1:mem ->
  Lemma
    (requires Seq.equal (as_seq h0 ctx) (as_seq h1 ctx) /\ Poly.state_inv_t h0 ctx)
    (ensures 
      Seq.index (Poly.as_get_acc h0 ctx) 0 == Seq.index (Poly.as_get_acc h1 ctx) 0 /\
      Seq.index (Poly.as_get_r h0 ctx) 0 == Seq.index (Poly.as_get_r h1 ctx) 0 /\
      Poly.state_inv_t h1 ctx
    )

let same_ctx_same_r_acc ctx h0 h1 = admit()
