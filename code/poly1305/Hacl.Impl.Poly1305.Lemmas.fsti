module Hacl.Impl.Poly1305.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

module BSeq = Lib.ByteSequence

val lemma_cast_vec128_to_vec64: b:vec_t U128 2 -> Lemma
 (let r = vec_v (cast U64 4 b) in
  let b = vec_v b in
  uint_v b.[0] == uint_v r.[0] + uint_v r.[1] * pow2 64 /\
  uint_v b.[1] == uint_v r.[2] + uint_v r.[3] * pow2 64)

val lemma_cast_vec64_to_vec128: b:vec_t U64 4 -> Lemma
 (let r = vec_v (cast U128 2 b) in
  let b = vec_v b in
  uint_v r.[0] == uint_v b.[0] + uint_v b.[1] * pow2 64 /\
  uint_v r.[1] == uint_v b.[2] + uint_v b.[3] * pow2 64)

val lemma_vec_interleave_low_cast_64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 -> Lemma
  (vec_v (cast U64 4 (vec_interleave_low (cast U128 2 b1) (cast U128 2 b2))) ==
   create4 (vec_v b1).[0] (vec_v b1).[1] (vec_v b2).[0] (vec_v b2).[1])

val lemma_vec_interleave_high_cast_64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 -> Lemma
  (vec_v (cast U64 4 (vec_interleave_high (cast U128 2 b1) (cast U128 2 b2))) ==
    create4 (vec_v b1).[2] (vec_v b1).[3] (vec_v b2).[2] (vec_v b2).[3])

val uint_from_bytes_le_lemma: b:lseq uint8 16 -> Lemma
 (let lo = BSeq.uint_from_bytes_le (sub b 0 8) in
  let hi = BSeq.uint_from_bytes_le (sub b 8 8) in
  BSeq.nat_from_bytes_le b == pow2 64 * uint_v hi + uint_v lo)

val uints_from_bytes_le_lemma64_1: b:lseq uint8 16 -> Lemma
 (let lo:lseq uint64 1 = BSeq.uints_from_bytes_le (sub b 0 8) in
  let hi:lseq uint64 1 = BSeq.uints_from_bytes_le (sub b 8 8) in
  BSeq.nat_from_bytes_le b == pow2 64 * uint_v hi.[0] + uint_v lo.[0])

val uints_from_bytes_le_lemma64_2: b:lseq uint8 32 -> Lemma
 (let lo:lseq uint64 2 = BSeq.uints_from_bytes_le (sub b 0 16) in
  let hi:lseq uint64 2 = BSeq.uints_from_bytes_le (sub b 16 16) in
  let b1 = BSeq.nat_from_bytes_le (sub b 0 16) in
  let b2 = BSeq.nat_from_bytes_le (sub b 16 16) in
  b1 == pow2 64 * uint_v lo.[1] + uint_v lo.[0] /\
  b2 == pow2 64 * uint_v hi.[1] + uint_v hi.[0])

val uints_from_bytes_le_lemma128_2: b:lseq uint8 64 -> Lemma
 (let lo:lseq uint128 2 = BSeq.uints_from_bytes_le (sub b 0 32) in
  let hi:lseq uint128 2 = BSeq.uints_from_bytes_le (sub b 32 32) in
  let b1 = BSeq.nat_from_bytes_le (sub b 0 16) in
  let b2 = BSeq.nat_from_bytes_le (sub b 16 16) in
  let b3 = BSeq.nat_from_bytes_le (sub b 32 16) in
  let b4 = BSeq.nat_from_bytes_le (sub b 48 16) in
  b1 == uint_v lo.[0] /\
  b2 == uint_v lo.[1] /\
  b3 == uint_v hi.[0] /\
  b4 == uint_v hi.[1])

val uint_to_bytes_le_lemma128: r:uint128 -> Lemma
  (BSeq.uint_to_bytes_le r == BSeq.nat_to_bytes_le 16 (uint_v r))

val uints_to_bytes_le_lemma64_1: lo:lseq uint64 1 -> hi:lseq uint64 1 -> Lemma
 (let b0 = BSeq.uints_to_bytes_le lo in
  let b1 = BSeq.uints_to_bytes_le hi in
  BSeq.nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0]) == concat b0 b1)

val uints_to_bytes_le_lemma64_2: r:lseq uint64 2 -> Lemma
  (BSeq.uints_to_bytes_le r == BSeq.nat_to_bytes_le 16 (uint_v r.[1] * pow2 64 + uint_v r.[0]))

val uints_to_bytes_le_lemma128_2: r:lseq uint128 2 -> Lemma
 (let b = BSeq.uints_to_bytes_le r in
  sub b 0 16 == BSeq.uint_to_bytes_le r.[0] /\
  sub b 16 16 == BSeq.uint_to_bytes_le r.[1])

val nat_from_bytes_le_eq_lemma: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  BSeq.nat_from_bytes_le b == BSeq.nat_from_bytes_le (update_sub tmp 0 len b))
