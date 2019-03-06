module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Poly = Spec.Poly1305
module PolyVec = Hacl.Spec.Poly1305.Vec

let update1_equiv (r:Poly.felem) (len:size_nat{len <= Poly.size_block}) (b:lbytes len) (acc:Poly.felem) 
  : Lemma (Poly.update1 r len b acc = PolyVec.update1 r len b acc)
  = admit()

// let poly_equiv (text:bytes) (acc:Poly.felem) (r:Poly.felem)
//   : Lemma (Poly.poly text acc r == PolyVec.poly #1 text (PolyVec.from_elem acc) (PolyVec.from_elem r)
//   = admit()


