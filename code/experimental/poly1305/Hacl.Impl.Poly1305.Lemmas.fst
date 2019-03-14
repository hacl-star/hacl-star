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

//Taken from Hacl.Impl.Curve25519.Lemmas
val lemma_uints64_from_bytes_le_nat_:
  #len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (ensures  nat_from_intseq_le_ (uints_from_bytes_le #U64 #_ #len b) == nat_from_intseq_le_ b)
let lemma_uints64_from_bytes_le_nat_ #len b = admit()

let uint_from_bytes_le_lemma b =
  let r1 = nat_from_bytes_le b in
  lemma_uints64_from_bytes_le_nat_ #2 b;
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

let uints_to_bytes_le_lemma64_1 lo hi = admit()

let uints_to_bytes_le_lemma64_2 r = admit()

let uints_to_bytes_le_lemma128_2 r = admit()

val lemma_nat_from_bytes_le_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_le_ b == 0)
let rec lemma_nat_from_bytes_le_zeroes len b =
  if len = 0 then ()
  else lemma_nat_from_bytes_le_zeroes (len-1) (Seq.slice b 1 len)

#set-options "--z3rlimit 50"

val lemma_nat_from_bytes_le_slice0: len:size_nat{len > 0} -> b:lseq uint8 len -> i:nat{0 < i /\ i < len} -> Lemma
  (pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b (i - 1) len) ==
   pow2 ((i - 1) * 8) * v b.[i - 1] + pow2 (i * 8) * nat_from_intseq_le_ (Seq.slice b i len))
let lemma_nat_from_bytes_le_slice0 len b i =
  assert (nat_from_intseq_le_ (Seq.slice b (i - 1) len) == v b.[i - 1] + pow2 8 * nat_from_intseq_le_ (Seq.slice b i len));
  assert (pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b (i - 1) len) == pow2 ((i - 1) * 8) * (v b.[i - 1] + pow2 8 * nat_from_intseq_le_ (Seq.slice b i len)));
  FStar.Math.Lemmas.distributivity_add_right (pow2 ((i - 1) * 8)) (v b.[i - 1]) (pow2 8 * nat_from_intseq_le_ (Seq.slice b i len));
  FStar.Math.Lemmas.paren_mul_right (pow2 ((i - 1) * 8)) (pow2 8) (nat_from_intseq_le_ (Seq.slice b i len));
  assert (pow2 ((i - 1) * 8) * (v b.[i - 1] + pow2 8 * nat_from_intseq_le_ (Seq.slice b i len)) ==
    pow2 ((i - 1) * 8) * v b.[i - 1] + pow2 ((i - 1) * 8) * pow2 8 * nat_from_intseq_le_ (Seq.slice b i len));
  FStar.Math.Lemmas.pow2_plus ((i - 1) * 8) 8;
  assert ((i-1) * 8 + 8 = i * 8);
  assert (pow2 ((i - 1) * 8) * pow2 8 == pow2 (i * 8));
  assert (pow2 ((i - 1) * 8) * (v b.[i - 1] + pow2 8 * nat_from_intseq_le_ (Seq.slice b i len)) ==
    pow2 ((i - 1) * 8) * v b.[i - 1] + pow2 (i * 8) * nat_from_intseq_le_ (Seq.slice b i len))

val lemma_nat_from_bytes_le_slice1: len:size_nat -> b:lseq uint8 len -> i:size_nat{0 < i /\ i < len} ->
  Lemma
    (requires (let b1 = Seq.slice b 0 i in
      nat_from_intseq_le_ b1 == nat_from_intseq_le_ (Seq.slice b1 0 (i - 1)) + pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b1 (i - 1) i)))
    (ensures nat_from_intseq_le_ (Seq.slice b 0 i) == nat_from_intseq_le_ (Seq.slice b 0 (i - 1)) + pow2 ((i - 1) * 8) * v b.[i - 1])
let lemma_nat_from_bytes_le_slice1 len b i = ()


val lemma_nat_from_bytes_le_slice: len:size_nat -> b:lseq uint8 len -> i:nat{i < len} ->
  Lemma (ensures (nat_from_intseq_le_ b == nat_from_intseq_le_ (Seq.slice b 0 i) + pow2 (i * 8) * nat_from_intseq_le_ (Seq.slice b i len)))
let rec lemma_nat_from_bytes_le_slice len b i =
  if len = 0 then ()
  else begin
    if i = 0 then begin
      assert (nat_from_intseq_le_ (Seq.slice b 0 0) = 0);
      assert_norm (pow2 (i * 8) = 1);
      assert (pow2 (i * 8) * nat_from_intseq_le_ (Seq.slice b 0 len) == nat_from_intseq_le_ b) end
    else begin
      lemma_nat_from_bytes_le_slice len b (i - 1);
      assert (nat_from_intseq_le_ b == nat_from_intseq_le_ (Seq.slice b 0 (i - 1)) + pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b (i - 1) len));
      lemma_nat_from_bytes_le_slice0 len b i;
      assert (
	nat_from_intseq_le_ (Seq.slice b 0 (i - 1)) + pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b (i - 1) len) ==
	nat_from_intseq_le_ (Seq.slice b 0 (i - 1)) + pow2 ((i - 1) * 8) * v b.[i - 1] + pow2 (i * 8) * nat_from_intseq_le_ (Seq.slice b i len));
      let b1 = Seq.slice b 0 i in
      lemma_nat_from_bytes_le_slice i b1 (i - 1);
      assert (nat_from_intseq_le_ b1 == nat_from_intseq_le_ (Seq.slice b1 0 (i - 1)) + pow2 ((i - 1) * 8) * nat_from_intseq_le_ (Seq.slice b1 (i - 1) i));
      lemma_nat_from_bytes_le_slice1 len b i
    end
  end

val lemma_mul_pow2_and_zero: a:nat -> Lemma (pow2 a * 0 = 0)
let lemma_mul_pow2_and_zero a = ()

val nat_from_bytes_le_eq_lemma_: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  BSeq.nat_from_intseq_le_ b == BSeq.nat_from_intseq_le_ (update_sub tmp 0 len b))
let nat_from_bytes_le_eq_lemma_ len b =
  let tmp = create 16 (u8 0) in
  let r = update_sub tmp 0 len b in
  assert (Seq.slice r 0 len == b);
  assert (forall (i:nat). len <= i /\ i < 16 ==> r.[i] == u8 0);
  assert (forall (i:nat). i < 16 - len ==> Seq.index (Seq.slice r len 16) i == u8 0);
  lemma_nat_from_bytes_le_slice 16 r len;
  assert (nat_from_intseq_le_ r == nat_from_intseq_le_ (Seq.slice r 0 len) + pow2 (len * 8) * nat_from_intseq_le_ (Seq.slice r len 16));
  assert (nat_from_intseq_le_ r == nat_from_intseq_le_ b + pow2 (len * 8) * nat_from_intseq_le_ (Seq.slice r len 16));
  lemma_nat_from_bytes_le_zeroes (16 - len) (Seq.slice r len 16);
  assert (nat_from_intseq_le_ (Seq.slice r len 16) = 0);
  assert (nat_from_intseq_le_ r == nat_from_intseq_le_ b + pow2 (len * 8) * 0);
  lemma_mul_pow2_and_zero (len * 8)

let nat_from_bytes_le_eq_lemma len b = nat_from_bytes_le_eq_lemma_ len b
