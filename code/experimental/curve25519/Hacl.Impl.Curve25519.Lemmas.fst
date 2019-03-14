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

val lemma_uints_from_bytes_le0: len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (forall (i:nat). i < len - 1 ==> (uints_from_bytes_le #U64 #_ #len b).[i + 1] == uint_from_bytes_le (sub b (8 * (i + 1)) 8))
let lemma_uints_from_bytes_le0 len b = ()

val lemma_uints_from_bytes_le1: len:size_nat{0 < len /\ 8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (forall (i:nat). i < len - 1 ==> Seq.index (Seq.slice (uints_from_bytes_le #U64 #_ #len b) 1 len) i == uint_from_bytes_le (sub b (8 * (i + 1)) 8))
let lemma_uints_from_bytes_le1 len b =
  lemma_uints_from_bytes_le0 len b

val lemma_uints_from_bytes_le_slice: len:size_nat{0 < len /\ 8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (Seq.slice (uints_from_bytes_le #U64 #_ #len b) 1 len == uints_from_bytes_le #U64 #_ #(len-1) (Seq.slice b 8 (8 * len)))
let lemma_uints_from_bytes_le_slice len b =
  let r = uints_from_bytes_le #U64 #_ #len b in
  let r1 = uints_from_bytes_le #U64 #_ #(len-1) (Seq.slice b 8 (8 * len)) in
  assert (forall (i:nat). i < len - 1 ==> r1.[i] == uint_from_bytes_le (sub b (8 * (i + 1)) 8));
  lemma_uints_from_bytes_le1 len b;
  eq_intro (Seq.slice r 1 len) r1

val lemma_uints64_from_bytes_le_nat0: len:size_nat{0 < len /\ 8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #len b) ==
   nat_from_intseq_le_ (Seq.slice b 0 8) + pow2 64 * nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #(len-1) (Seq.slice b 8 (8 * len))))
let lemma_uints64_from_bytes_le_nat0 len b =
  let r = uints_from_bytes_le #U64 #_ #len b in
  let r2 : lseq uint64 (len - 1) = Seq.slice r 1 len in
  let b1 : lseq uint8 (8 * (len - 1)) = Seq.slice b 8 (8 * len) in
  let r1 = uints_from_bytes_le #U64 #_ #(len-1) b1 in
  lemma_uints_from_bytes_le_slice len b;
  assert (nat_from_intseq_le_ r == v r.[0] + pow2 64 * nat_from_intseq_le_ r2);
  assert (nat_from_intseq_le_ (Seq.slice b 0 8) == v r.[0])

val lemma_uints64_from_bytes_le_nat_:
  #len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (ensures nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #len b) == nat_from_intseq_le_ b)
let rec lemma_uints64_from_bytes_le_nat_ #len b =
  if len = 0 then ()
  else begin
    let b1 = Seq.slice b 8 (8 * len) in
    lemma_uints64_from_bytes_le_nat_ #(len - 1) b1;
    assert (nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #(len-1) b1) == nat_from_intseq_le_ b1);
    nat_from_bytes_le_slice_lemma #_ #(8 * len) b 8;
    lemma_uints64_from_bytes_le_nat0 len b
  end

let lemma_uints64_from_bytes_le_nat #len b = lemma_uints64_from_bytes_le_nat_ #len b
