module Hacl.Impl.Curve25519.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

friend Lib.ByteSequence

#set-options "--z3rlimit 50 --max_fuel 1"

let lemma_nat_from_uints64_le_4 b =
  let res = nat_from_intseq_le b in
  assert (res == v b.[0] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 1 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 1 4) == v b.[1] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 2 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 2 4) == v b.[2] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 3 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 3 4) == v b.[3]);
  assert (res == v b.[0] + pow2 64 * (v b.[1] + pow2 64 * (v b.[2] + pow2 64 * v b.[3])))

let lemma_nat_to_uints64_le_4 b n =
  let b1 = nat_to_intseq_le 4 n in
  nat_from_intseq_le_inj b1 b
