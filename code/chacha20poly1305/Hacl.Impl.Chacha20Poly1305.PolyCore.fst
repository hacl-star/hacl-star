module Hacl.Impl.Chacha20Poly1305.PolyCore

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
open Hacl.Spec.Poly1305.Equiv
open Hacl.Impl.Chacha20Poly1305.PolyLemmas

let poly1305_padded ctx len text tmp = admit()

let poly1305_init ctx k = Poly.poly1305_init ctx k
  
let update1 ctx len text = 
  let h0 = ST.get() in
  update1_equiv (Poly.as_get_r h0 ctx) (v len) (as_seq h0 text) (Poly.as_get_acc h0 ctx);
  Poly.poly1305_update ctx len text

let finish ctx k out = Poly.poly1305_finish out k ctx
