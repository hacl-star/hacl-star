module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Poly = Spec.Poly1305
module PolyVec = Hacl.Spec.Poly1305.Vec
open Hacl.Impl.Poly1305.Fields

// Running poly1305_update on one single block is equivalent to running update1
let update1_equiv 
  (r:PolyVec.elem (width M32)) 
  (len:size_nat{len <= Poly.size_block}) 
  (b:lbytes len)
  (acc:PolyVec.elem (width M32))
  : Lemma (
    Poly.update1 (Seq.index r 0) len b (Seq.index acc 0) = PolyVec.poly_update b acc r)
  = admit()

// let poly_equiv (text:bytes) (acc:Poly.felem) (r:Poly.felem)
//   : Lemma (Poly.poly text acc r == PolyVec.poly #1 text (PolyVec.from_elem acc) (PolyVec.from_elem r)
//   = admit()


