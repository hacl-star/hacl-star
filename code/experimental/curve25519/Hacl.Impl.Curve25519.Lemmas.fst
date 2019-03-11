module Hacl.Impl.Curve25519.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

friend Lib.ByteSequence

let lemma_nat_from_uints64_le_4 b =
  let res = nat_from_intseq_le b in
  assert (res == v b.[0] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 1 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 1 4) == v b.[1] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 2 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 2 4) == v b.[2] + pow2 64 * (nat_from_intseq_le_ (Seq.slice b 3 4)));
  assert (nat_from_intseq_le_ (Seq.slice b 3 4) == v b.[3]);
  assert (res == v b.[0] + pow2 64 * (v b.[1] + pow2 64 * (v b.[2] + pow2 64 * v b.[3])))

val lemma_nat_from_bytes_le_unroll8:
  #len:size_nat{0 < len /\ 8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (ensures nat_from_intseq_le_ b == nat_from_intseq_le (Seq.slice b 0 8) + pow2 64 * nat_from_intseq_le_ (Seq.slice b 8 (8 * len)))
let lemma_nat_from_bytes_le_unroll8 #len b = admit()
  // assert (nat_from_intseq_le_ b == v b.[0] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 1 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 1 (8 * len)) == v b.[1] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 2 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 2 (8 * len)) == v b.[2] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 3 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 3 (8 * len)) == v b.[3] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 4 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 4 (8 * len)) == v b.[4] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 5 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 5 (8 * len)) == v b.[5] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 6 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 6 (8 * len)) == v b.[6] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 7 (8 * len)));
  // assert (nat_from_intseq_le_ (Seq.slice b 7 (8 * len)) == v b.[7] + pow2 8 * nat_from_intseq_le_ (Seq.slice b 8 (8 * len)));

val lemma_uints64_from_bytes_le_slice:
  #len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> i:size_nat{i <= len} -> Lemma
  (ensures (
    Seq.slice (uints_from_bytes_le #U64 #_ #len b) i len ==
    uints_from_bytes_le #U64 #_ #(len - i) (Seq.slice b (8 * i) (8 * len))))
let lemma_uints64_from_bytes_le_slice #len b i = admit()

#set-options "--z3rlimit 50"

val lemma_uints64_from_bytes_le_nat_:
  #len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (ensures  nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #len b) == nat_from_intseq_le_ b)
let rec lemma_uints64_from_bytes_le_nat_ #len b =
  if len = 0 then ()
  else begin
    let b1 = Seq.slice b 8 (8 * len) in
    lemma_uints64_from_bytes_le_nat_ #(len - 1) b1;
    assert (nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #(len-1) b1) == nat_from_intseq_le_ b1);
    lemma_nat_from_bytes_le_unroll8 #len b;
    assert (nat_from_intseq_le_ b == nat_from_intseq_le (Seq.slice b 0 8) + pow2 64 * (nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #(len-1) b1)));
    let b64 = uints_from_bytes_le #U64 #_ #len b in
    assert (v b64.[0] == nat_from_intseq_le (Seq.slice b 0 8));
    lemma_uints64_from_bytes_le_slice #len b 1;
    assert (Seq.slice b64 1 len == uints_from_bytes_le #U64 #_ #(len - 1) b1)
  end

let lemma_uints64_from_bytes_le_nat #len b = lemma_uints64_from_bytes_le_nat_ #len b
