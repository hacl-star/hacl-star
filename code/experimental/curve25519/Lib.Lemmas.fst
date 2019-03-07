module Lib.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module BSeq = Lib.ByteSequence

val lemma_nat_from_uints64_le_4: b:lseq uint64 4 ->
  Lemma (BSeq.nat_from_intseq_le b ==
    v b.[0] + v b.[1] * pow2 64 +
    v b.[2] * pow2 64 * pow2 64 + v b.[3] * pow2 64 * pow2 64 * pow2 64)
let lemma_nat_from_uints64_le_4 b = admit()
