module Vale.LowStarHelpers

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack

(* This should be provable in the F* library at some point *)
assume
val lemma_different_preorders_different_buffers (b:B.buffer UInt8.t) (b':IB.ibuffer UInt8.t) : Lemma
  (~ (eq3 #(B.buffer UInt8.t) #(IB.ibuffer UInt8.t) b  b'))
