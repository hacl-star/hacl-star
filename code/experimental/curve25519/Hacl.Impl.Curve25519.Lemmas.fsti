module Hacl.Impl.Curve25519.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

val lemma_nat_from_uints64_le_4: b:lseq uint64 4 -> Lemma
  (nat_from_intseq_le b == v b.[0] + v b.[1] * pow2 64 +
    v b.[2] * pow2 64 * pow2 64 + v b.[3] * pow2 64 * pow2 64 * pow2 64)

val lemma_uints64_from_bytes_le_nat:
  #len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (ensures  nat_from_intseq_le (uints_from_bytes_le #U64 #SEC #len b) == nat_from_bytes_le b)
