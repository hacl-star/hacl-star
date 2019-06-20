module Hacl.Impl.Poly1305.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open Lib.ByteSequence

friend Lib.ByteSequence

let lemma_cast_vec128_to_vec64 b = cast_vec_u128_to_u64_lemma b

let lemma_cast_vec64_to_vec128 b = cast_vec_u64_to_u128_lemma #2 b

let lemma_vec_interleave_low_cast_64_4 b1 b2 =
  let r1 = cast U128 2 b1 in
  lemma_cast_vec64_to_vec128 b1;
  let r2 = cast U128 2 b2 in
  lemma_cast_vec64_to_vec128 b2;
  let r3 = vec_interleave_low r1 r2 in
  vec_interleave_low_lemma2 r1 r2;
  let r4 = cast U64 4 r3 in
  lemma_cast_vec128_to_vec64 r3;
  uintv_extensionality (vec_v r4).[0] (vec_v b1).[0];
  uintv_extensionality (vec_v r4).[1] (vec_v b1).[1];
  uintv_extensionality (vec_v r4).[2] (vec_v b2).[0];
  uintv_extensionality (vec_v r4).[3] (vec_v b2).[1];
  eq_intro (vec_v r4) (create4 (vec_v b1).[0] (vec_v b1).[1] (vec_v b2).[0] (vec_v b2).[1])

let lemma_vec_interleave_high_cast_64_4 b1 b2 =
  let r1 = cast U128 2 b1 in
  lemma_cast_vec64_to_vec128 b1;
  let r2 = cast U128 2 b2 in
  lemma_cast_vec64_to_vec128 b2;
  let r3 = vec_interleave_high r1 r2 in
  vec_interleave_high_lemma2 r1 r2;
  let r4 = cast U64 4 r3 in
  lemma_cast_vec128_to_vec64 r3;
  uintv_extensionality (vec_v r4).[0] (vec_v b1).[2];
  uintv_extensionality (vec_v r4).[1] (vec_v b1).[3];
  uintv_extensionality (vec_v r4).[2] (vec_v b2).[2];
  uintv_extensionality (vec_v r4).[3] (vec_v b2).[3];
  eq_intro (vec_v r4) (create4 (vec_v b1).[2] (vec_v b1).[3] (vec_v b2).[2] (vec_v b2).[3])

#set-options "--z3rlimit 50 --max_fuel 1"

let uint_from_bytes_le_lemma b =
  let r1 = nat_from_bytes_le b in
  uints_from_bytes_le_nat_lemma #U64 #_ #2 b;
  assert (r1 == nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #2 b));
  let r2 = uints_from_bytes_le #U64 #_ #2 b in
  assert (r2.[0] == uint_from_bytes_le (sub b 0 8));
  assert (r2.[1] == uint_from_bytes_le (sub b 8 8));
  assert (nat_from_intseq_le_ r2 == v r2.[0] + pow2 64 * nat_from_intseq_le_ (Seq.slice r2 1 2));
  assert (nat_from_intseq_le_ (Seq.slice r2 1 2) == v r2.[1])
  
let uints_from_bytes_le_lemma64_1 b =
  uint_from_bytes_le_lemma b

let uints_from_bytes_le_lemma64_2 b =
  uint_from_bytes_le_lemma (sub b 0 16);
  uint_from_bytes_le_lemma (sub b 16 16)

let uints_from_bytes_le_lemma128_2 b = ()

let uint_to_bytes_le_lemma128 r = ()

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

let uints_to_bytes_le_lemma128_2 r =
  // ibid.
  admit ()

#push-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0"
val lemma_nat_from_bytes_le_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_le_ b == 0)
let rec lemma_nat_from_bytes_le_zeroes len b =
  if len = 0 then ()
  else lemma_nat_from_bytes_le_zeroes (len-1) (Seq.slice b 1 len)
#pop-options

val nat_from_bytes_le_eq_lemma_: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  BSeq.nat_from_intseq_le_ b == BSeq.nat_from_intseq_le_ (update_sub tmp 0 len b))
let nat_from_bytes_le_eq_lemma_ len b =
  let tmp = create 16 (u8 0) in
  let r = update_sub tmp 0 len b in
  assert (Seq.slice r 0 len == b);
  assert (forall (i:nat). len <= i /\ i < 16 ==> r.[i] == u8 0);
  assert (forall (i:nat). i < 16 - len ==> Seq.index (Seq.slice r len 16) i == u8 0);
  nat_from_bytes_le_slice_lemma #_ #16 r len;
  assert (nat_from_intseq_le_ r == nat_from_intseq_le_ (Seq.slice r 0 len) + pow2 (len * 8) * nat_from_intseq_le_ (Seq.slice r len 16));
  assert (nat_from_intseq_le_ r == nat_from_intseq_le_ b + pow2 (len * 8) * nat_from_intseq_le_ (Seq.slice r len 16));
  lemma_nat_from_bytes_le_zeroes (16 - len) (Seq.slice r len 16)

let nat_from_bytes_le_eq_lemma len b = nat_from_bytes_le_eq_lemma_ len b
