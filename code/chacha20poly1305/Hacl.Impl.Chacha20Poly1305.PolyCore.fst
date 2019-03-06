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

let same_ctx_same_r_acc #s ctx h0 h1 = admit()

let poly1305_padded #s ctx len text tmp = admit()

let poly1305_init #s ctx k = Poly.poly1305_init ctx k
  
let update1 #s ctx len text = 
  let h0 = ST.get() in
  assume (Poly.state_inv_t h0 ctx);
  Poly.poly1305_update ctx len text;
  admit()

let finish #s ctx k out = admit()
