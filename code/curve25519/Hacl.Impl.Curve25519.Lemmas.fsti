module Hacl.Impl.Curve25519.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

val lemma_nat_from_uints64_le_4: b:lseq uint64 4 -> Lemma
  (nat_from_intseq_le b == v b.[0] + v b.[1] * pow2 64 +
    v b.[2] * pow2 64 * pow2 64 + v b.[3] * pow2 64 * pow2 64 * pow2 64)

val lemma_nat_to_uints64_le_4: b:lseq uint64 4 -> n:nat{n < pow2 256} ->
  Lemma
    (requires n == nat_from_intseq_le b)
    (ensures  b == nat_to_intseq_le 4 n)
