module Hacl.Impl.Poly1305.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 50 --max_fuel 1"

let uint_from_bytes_le_lemma b =
  let r1 = nat_from_bytes_le b in
  let r2 = uints_from_bytes_le #U64 #SEC #2 b in
  uints_from_bytes_le_nat_lemma #U64 #SEC #2 b;
  assert (r1 == nat_from_intseq_le r2);
  nat_from_intseq_le_slice_lemma #U64 #SEC #2 r2 1;
  assert (r1 == nat_from_intseq_le (Seq.slice r2 0 1) + pow2 64 * nat_from_intseq_le #U64 #SEC (Seq.slice r2 1 2));
  nat_from_intseq_le_lemma0 (Seq.slice r2 0 1);
  nat_from_intseq_le_lemma0 (Seq.slice r2 1 2);
  assert (r1 == uint_v r2.[0] + pow2 64 * uint_v r2.[1]);
  Classical.forall_intro (index_uints_from_bytes_le #U64 #SEC #2 b)

let uints_from_bytes_le_lemma64_1 b =
  index_uints_from_bytes_le #U64 #SEC #1 (sub b 0 8) 0;
  index_uints_from_bytes_le #U64 #SEC #1 (sub b 8 8) 0;
  uint_from_bytes_le_lemma b

let uints_from_bytes_le_lemma64_2 b =
  Classical.forall_intro (index_uints_from_bytes_le #U64 #SEC #2 (sub b 0 16));
  Classical.forall_intro (index_uints_from_bytes_le #U64 #SEC #2 (sub b 16 16));
  uint_from_bytes_le_lemma (sub b 0 16);
  uint_from_bytes_le_lemma (sub b 16 16)

let uints_from_bytes_le_lemma64_4 b =
  Classical.forall_intro (index_uints_from_bytes_le #U64 #SEC #4 (sub b 0 32));
  Classical.forall_intro (index_uints_from_bytes_le #U64 #SEC #4 (sub b 32 32));
  uint_from_bytes_le_lemma (sub b 0 16);
  uint_from_bytes_le_lemma (sub b 16 16);
  uint_from_bytes_le_lemma (sub b 32 16);
  uint_from_bytes_le_lemma (sub b 48 16)


let uints64_to_bytes_le_lemma lo hi =
  let lp = nat_to_bytes_le #SEC 16 (v hi * pow2 64 + v lo) in
  let rp = concat (uint_to_bytes_le lo) (uint_to_bytes_le hi) in
  assert (nat_from_bytes_le lp == v hi * pow2 64 + v lo);
  Seq.append_slices (uint_to_bytes_le lo) (uint_to_bytes_le hi);
  nat_from_intseq_le_slice_lemma #U8 #SEC #16 rp 8;
  assert (nat_from_bytes_le rp == nat_from_bytes_le (Seq.slice rp 0 8) + pow2 (8 * 8) * nat_from_bytes_le (Seq.slice rp 8 16));
  assert (nat_from_bytes_le rp == nat_from_bytes_le (uint_to_bytes_le lo) + pow2 64 * nat_from_bytes_le (uint_to_bytes_le hi));
  lemma_uint_to_bytes_le_preserves_value lo;
  lemma_uint_to_bytes_le_preserves_value hi;
  nat_from_intseq_le_inj lp rp


module BF = Vale.Arch.BufferFriend

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let uints_to_bytes_le_lemma64_1 lo hi =
  // Sketch:
  //
  // let b0 = BSeq.uints_to_bytes_le lo in
  // let b1 = BSeq.uints_to_bytes_le hi in
  // calc (==) {
  //   nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0])
  // (==) { Vale.Arch.BufferFriend }
  //   let lo = uints_from_bytes_le (uints_to_bytes_le lo) in
  //   let hi = uints_from_bytes_le (uints_to_bytes_le hi) in
  //   nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0])
  // (==) { }
  //   let b = concat (uints_to_bytes_le lo) (uints_to_bytes_le hi) in
  //   let lo = uints_from_bytes_le (sub b 0 8) in
  //   let hi = uints_from_bytes_le (sub b 8 8) in
  //   nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0])
  // (==) { lemma_uints_from_bytes_le_lemma_64_1 (concat b0 b1) }
  //   nat_to_bytes_le (nat_from_bytes_le 16 (concat b0 b1));
  // (==) { Vale.Arch.BufferFriend }
  //   n_to_le (le_to_n 16 b)
  // (==) { FStar.Endianness }
  //   b
  // (==) { def }
  //   concat
  admit ()

let uints_to_bytes_le_lemma64_2 r =
  // Similarly mundane. The Lib.ByteSequence library currently lacks enough
  // lemmas to prove this simply.
  admit ()

val lemma_nat_from_bytes_le_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_le b == 0)
let rec lemma_nat_from_bytes_le_zeroes len b =
  if len = 0 then ()
  else begin
    nat_from_intseq_le_slice_lemma #U8 #SEC #len b 1;
    nat_from_intseq_le_lemma0 (Seq.slice b 0 1);
    lemma_nat_from_bytes_le_zeroes (len-1) (Seq.slice b 1 len) end

val nat_from_bytes_le_eq_lemma_: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  BSeq.nat_from_intseq_le b == BSeq.nat_from_intseq_le (update_sub tmp 0 len b))
let nat_from_bytes_le_eq_lemma_ len b =
  let tmp = create 16 (u8 0) in
  let r = update_sub tmp 0 len b in
  assert (Seq.slice r 0 len == b);
  assert (forall (i:nat). len <= i /\ i < 16 ==> r.[i] == u8 0);
  assert (forall (i:nat). i < 16 - len ==> Seq.index (Seq.slice r len 16) i == u8 0);
  nat_from_intseq_le_slice_lemma #U8 #SEC #16 r len;
  assert (nat_from_intseq_le r == nat_from_intseq_le (Seq.slice r 0 len) + pow2 (len * 8) * nat_from_intseq_le (Seq.slice r len 16));
  assert (nat_from_intseq_le r == nat_from_intseq_le b + pow2 (len * 8) * nat_from_intseq_le (Seq.slice r len 16));
  lemma_nat_from_bytes_le_zeroes (16 - len) (Seq.slice r len 16)

let nat_from_bytes_le_eq_lemma len b = nat_from_bytes_le_eq_lemma_ len b
