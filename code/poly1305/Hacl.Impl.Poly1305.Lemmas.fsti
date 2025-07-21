module Hacl.Impl.Poly1305.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

val uint_from_bytes_le_lemma: b:lseq uint8 16 -> Lemma
 (let lo = uint_from_bytes_le #U64 (sub b 0 8) in
  let hi = uint_from_bytes_le #U64 (sub b 8 8) in
  nat_from_bytes_le b == pow2 64 * uint_v hi + uint_v lo)

val uints_from_bytes_le_lemma64_1: b:lseq uint8 16 -> Lemma
 (let lo:lseq uint64 1 = uints_from_bytes_le (sub b 0 8) in
  let hi:lseq uint64 1 = uints_from_bytes_le (sub b 8 8) in
  nat_from_bytes_le b == pow2 64 * uint_v hi.[0] + uint_v lo.[0])

val uints_from_bytes_le_lemma64_2: b:lseq uint8 32 -> Lemma
 (let lo:lseq uint64 2 = uints_from_bytes_le (sub b 0 16) in
  let hi:lseq uint64 2 = uints_from_bytes_le (sub b 16 16) in
  let b1 = nat_from_bytes_le (sub b 0 16) in
  let b2 = nat_from_bytes_le (sub b 16 16) in
  b1 == pow2 64 * uint_v lo.[1] + uint_v lo.[0] /\
  b2 == pow2 64 * uint_v hi.[1] + uint_v hi.[0])

val uints_from_bytes_le_lemma64_4: b:lseq uint8 64 -> Lemma
 (let lo:lseq uint64 4 = uints_from_bytes_le (sub b 0 32) in
  let hi:lseq uint64 4 = uints_from_bytes_le (sub b 32 32) in
  let b1 = nat_from_bytes_le (sub b 0 16) in
  let b2 = nat_from_bytes_le (sub b 16 16) in
  let b3 = nat_from_bytes_le (sub b 32 16) in
  let b4 = nat_from_bytes_le (sub b 48 16) in
  b1 == pow2 64 * uint_v lo.[1] + uint_v lo.[0] /\
  b2 == pow2 64 * uint_v lo.[3] + uint_v lo.[2] /\
  b3 == pow2 64 * uint_v hi.[1] + uint_v hi.[0] /\
  b4 == pow2 64 * uint_v hi.[3] + uint_v hi.[2])

val uints64_to_bytes_le_lemma: lo:uint64 -> hi:uint64 -> Lemma
  (concat (uint_to_bytes_le lo) (uint_to_bytes_le hi) == nat_to_bytes_le 16 (v hi * pow2 64 + v lo))

val lemma_nat_from_bytes_le_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_le b == 0)

val nat_from_bytes_le_eq_lemma_: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  nat_from_intseq_le b == nat_from_intseq_le (update_sub tmp 0 len b))

val nat_from_bytes_le_eq_lemma: len:size_nat{len < 16} -> b:lseq uint8 len -> Lemma
 (let tmp = create 16 (u8 0) in
  nat_from_bytes_le b == nat_from_bytes_le (update_sub tmp 0 len b))
