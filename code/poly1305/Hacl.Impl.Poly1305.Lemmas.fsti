module Hacl.Impl.Poly1305.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

module BSeq = Lib.ByteSequence

val uint_from_bytes_le_lemma: b:lseq uint8 16 -> Lemma
 (let lo = BSeq.uint_from_bytes_le #U64 (sub b 0 8) in
  let hi = BSeq.uint_from_bytes_le #U64 (sub b 8 8) in
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
val uints_from_bytes_le_lemma64_4: b:lseq uint8 64 -> Lemma
 (let lo:lseq uint64 4 = BSeq.uints_from_bytes_le (sub b 0 32) in
  let hi:lseq uint64 4 = BSeq.uints_from_bytes_le (sub b 32 32) in
  let b1 = BSeq.nat_from_bytes_le (sub b 0 16) in
  let b2 = BSeq.nat_from_bytes_le (sub b 16 16) in
  let b3 = BSeq.nat_from_bytes_le (sub b 32 16) in
  let b4 = BSeq.nat_from_bytes_le (sub b 48 16) in
  b1 == pow2 64 * uint_v lo.[1] + uint_v lo.[0] /\
  b2 == pow2 64 * uint_v lo.[3] + uint_v lo.[2] /\
  b3 == pow2 64 * uint_v hi.[1] + uint_v hi.[0] /\
  b4 == pow2 64 * uint_v hi.[3] + uint_v hi.[2])

val uints64_to_bytes_le_lemma: lo:uint64 -> hi:uint64 -> Lemma
  (concat (BSeq.uint_to_bytes_le lo) (BSeq.uint_to_bytes_le hi) == BSeq.nat_to_bytes_le 16 (v hi * pow2 64 + v lo))

val uints_to_bytes_le_lemma64_1: lo:lseq uint64 1 -> hi:lseq uint64 1 -> Lemma
 (let b0 = BSeq.uints_to_bytes_le lo in
  let b1 = BSeq.uints_to_bytes_le hi in
  BSeq.nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0]) == concat b0 b1)

val uints_to_bytes_le_lemma64_2: r:lseq uint64 2 -> Lemma
  (BSeq.uints_to_bytes_le r == BSeq.nat_to_bytes_le 16 (uint_v r.[1] * pow2 64 + uint_v r.[0]))

val nat_from_bytes_le_eq_lemma: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  BSeq.nat_from_bytes_le b == BSeq.nat_from_bytes_le (update_sub tmp 0 len b))
