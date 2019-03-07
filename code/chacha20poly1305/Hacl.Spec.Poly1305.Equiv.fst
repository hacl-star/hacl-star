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

let poly_equiv
  (len:size_nat)
  (text:lbytes len)
  (acc:PolyVec.elem (width M32))
  (r:PolyVec.elem (width M32))
  : Lemma (Poly.poly text (Seq.index acc 0) (Seq.index r 0) == 
    PolyVec.poly_update #1 text acc r)
  = admit()


