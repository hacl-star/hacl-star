module Hacl.Impl.Curve25519.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 50 --max_fuel 1"

val lemma_nat_from_uints64_le_4: b:lseq uint64 4 -> Lemma
  (nat_from_intseq_le b == v b.[0] + v b.[1] * pow2 64 +
    v b.[2] * pow2 64 * pow2 64 + v b.[3] * pow2 64 * pow2 64 * pow2 64)

let lemma_nat_from_uints64_le_4 b =
  let res = nat_from_intseq_le b in
  nat_from_intseq_le_slice_lemma b 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 0 1);
  assert (res == v b.[0] + pow2 64 * (nat_from_intseq_le (Seq.slice b 1 4)));

  nat_from_intseq_le_slice_lemma #U64 #SEC #3 (Seq.slice b 1 4) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 1 2);
  assert (nat_from_intseq_le (Seq.slice b 1 4) == v b.[1] + pow2 64 * (nat_from_intseq_le (Seq.slice b 2 4)));

  nat_from_intseq_le_slice_lemma #U64 #SEC #2 (Seq.slice b 2 4) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 2 3);
  assert (nat_from_intseq_le (Seq.slice b 2 4) == v b.[2] + pow2 64 * (nat_from_intseq_le (Seq.slice b 3 4)));

  nat_from_intseq_le_lemma0 (Seq.slice b 3 4);
  assert (res == v b.[0] + pow2 64 * (v b.[1] + pow2 64 * (v b.[2] + pow2 64 * v b.[3])))
