module Lib.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
open LSeq

val vec_interleave_low_lemma64_2: b1:vec_t U64 2 -> b2:vec_t U64 2 ->
  Lemma (vec_v (vec_interleave_low b1 b2) == create2 (vec_v b1).[0] (vec_v b2).[0])
let vec_interleave_low_lemma64_2 b1 b2 = admit()

val vec_interleave_high_lemma64_2: b1:vec_t U64 2 -> b2:vec_t U64 2 ->
  Lemma (vec_v (vec_interleave_high b1 b2) == create2 (vec_v b1).[1] (vec_v b2).[1])
let vec_interleave_high_lemma64_2 b1 b2 = admit()

val vec_interleave_low_lemma64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 ->
  Lemma (vec_v (vec_interleave_low b1 b2) == create4 (vec_v b1).[0] (vec_v b2).[0] (vec_v b1).[2] (vec_v b2).[2])
let vec_interleave_low_lemma64_4 b1 b2 = admit()

val vec_interleave_high_lemma64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 ->
  Lemma (vec_v (vec_interleave_high b1 b2) == create4 (vec_v b1).[1] (vec_v b2).[1] (vec_v b1).[3] (vec_v b2).[3])
let vec_interleave_high_lemma64_4 b1 b2 = admit()

val vec_interleave_low_lemma128_2: b1:vec_t U128 2 -> b2:vec_t U128 2 ->
  Lemma (vec_v (vec_interleave_low b1 b2) == create2 (vec_v b1).[0] (vec_v b2).[0])
let vec_interleave_low_lemma128_2 b1 b2 = admit()

val vec_interleave_high_lemma128_2: b1:vec_t U128 2 -> b2:vec_t U128 2 ->
  Lemma (vec_v (vec_interleave_high b1 b2) == create2 (vec_v b1).[1] (vec_v b2).[1])
let vec_interleave_high_lemma128_2 b1 b2 = admit()

val lemma_cast_vec128_to_vec64: b:vec_t U128 2 ->
  Lemma (
    let r = vec_v (cast U64 4 b) in
    let b = vec_v b in
    uint_v b.[0] == uint_v r.[0] + uint_v r.[1] * pow2 64 /\
    uint_v b.[1] == uint_v r.[2] + uint_v r.[3] * pow2 64)
let lemma_cast_vec128_to_vec64 b = admit()

val lemma_cast_vec64_to_vec128: b:vec_t U64 4 ->
  Lemma (
    let r = vec_v (cast U128 2 b) in
    let b = vec_v b in
    uint_v r.[0] == uint_v b.[0] + uint_v b.[1] * pow2 64 /\
    uint_v r.[1] == uint_v b.[2] + uint_v b.[3] * pow2 64)
let lemma_cast_vec64_to_vec128 b = admit()

val lemma_vec_interleave_low_cast_64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 ->
  Lemma (
    vec_v (cast U64 4 (vec_interleave_low (cast U128 2 b1) (cast U128 2 b2))) ==
    create4 (vec_v b1).[0] (vec_v b1).[1] (vec_v b2).[0] (vec_v b2).[1])
let lemma_vec_interleave_low_cast_64_4 b1 b2 = admit()

val lemma_vec_interleave_high_cast_64_4: b1:vec_t U64 4 -> b2:vec_t U64 4 ->
  Lemma (
    vec_v (cast U64 4 (vec_interleave_high (cast U128 2 b1) (cast U128 2 b2))) ==
    create4 (vec_v b1).[2] (vec_v b1).[3] (vec_v b2).[2] (vec_v b2).[3])
let lemma_vec_interleave_high_cast_64_4 b1 b2 = admit()

val uint_from_bytes_le_lemma: b:LSeq.lseq uint8 16 ->
  Lemma (
    let lo = BSeq.uint_from_bytes_le (LSeq.sub b 0 8) in
    let hi = BSeq.uint_from_bytes_le (LSeq.sub b 8 8) in
    BSeq.nat_from_bytes_le b == pow2 64 * uint_v hi + uint_v lo)
let uint_from_bytes_le_lemma b = admit()

val uints_from_bytes_le_lemma64_1: b:LSeq.lseq uint8 16 ->
  Lemma (
    let lo:LSeq.lseq uint64 1 = BSeq.uints_from_bytes_le (LSeq.sub b 0 8) in
    let hi:LSeq.lseq uint64 1 = BSeq.uints_from_bytes_le (LSeq.sub b 8 8) in
    BSeq.nat_from_bytes_le b == pow2 64 * uint_v hi.[0] + uint_v lo.[0])
let uints_from_bytes_le_lemma64_1 b = admit()

val uints_from_bytes_le_lemma64_2: b:LSeq.lseq uint8 32 ->
  Lemma (
    let lo:LSeq.lseq uint64 2 = BSeq.uints_from_bytes_le (LSeq.sub b 0 16) in
    let hi:LSeq.lseq uint64 2 = BSeq.uints_from_bytes_le (LSeq.sub b 16 16) in
    let b1 = BSeq.nat_from_bytes_le (LSeq.sub b 0 16) in
    let b2 = BSeq.nat_from_bytes_le (LSeq.sub b 16 16) in
    b1 == pow2 64 * uint_v lo.[1] + uint_v lo.[0] /\
    b2 == pow2 64 * uint_v hi.[1] + uint_v hi.[0])
let uints_from_bytes_le_lemma64_2 b = admit()

val uints_from_bytes_le_lemma128_2: b:LSeq.lseq uint8 64 ->
  Lemma (
    let lo:LSeq.lseq uint128 2 = BSeq.uints_from_bytes_le (LSeq.sub b 0 32) in
    let hi:LSeq.lseq uint128 2 = BSeq.uints_from_bytes_le (LSeq.sub b 32 32) in
    let b1 = BSeq.nat_from_bytes_le (LSeq.sub b 0 16) in
    let b2 = BSeq.nat_from_bytes_le (LSeq.sub b 16 16) in
    let b3 = BSeq.nat_from_bytes_le (LSeq.sub b 32 16) in
    let b4 = BSeq.nat_from_bytes_le (LSeq.sub b 48 16) in
    b1 == uint_v lo.[0] /\
    b2 == uint_v lo.[1] /\
    b3 == uint_v hi.[0] /\
    b4 == uint_v hi.[1])
let uints_from_bytes_le_lemma128_2 b = admit()

val uint_to_bytes_le_lemma128: r:uint128 ->
  Lemma (BSeq.uint_to_bytes_le r == BSeq.nat_to_bytes_le 16 (uint_v r))
let uint_to_bytes_le_lemma128 r = admit()

val uints_to_bytes_le_lemma64_1: lo:LSeq.lseq uint64 1 -> hi:LSeq.lseq uint64 1 ->
  Lemma (
    let b0 = BSeq.uints_to_bytes_le lo in
    let b1 = BSeq.uints_to_bytes_le hi in
    BSeq.nat_to_bytes_le 16 (uint_v hi.[0] * pow2 64 + uint_v lo.[0]) == LSeq.concat b0 b1)
let uints_to_bytes_le_lemma64_1 lo hi = admit()

val uints_to_bytes_le_lemma64_2: r:LSeq.lseq uint64 2 ->
  Lemma (
    BSeq.uints_to_bytes_le r == BSeq.nat_to_bytes_le 16 (uint_v r.[1] * pow2 64 + uint_v r.[0]))
let uints_to_bytes_le_lemma64_2 r = admit()

val uints_to_bytes_le_lemma128_2: r:LSeq.lseq uint128 2 ->
  Lemma (
    let b = BSeq.uints_to_bytes_le r in
    LSeq.sub b 0 16 == BSeq.uint_to_bytes_le r.[0] /\
    LSeq.sub b 16 16 == BSeq.uint_to_bytes_le r.[1])
let uints_to_bytes_le_lemma128_2 r = admit()

val eq_mask_logand_lemma: a:uint64 -> b:uint64 -> c:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a = v b then
      v (c `logand` (eq_mask a b)) == v c
    else
      v (c `logand` (eq_mask a b)) == 0))
  [SMTPat (c `logand` (eq_mask a b))]
let eq_mask_logand_lemma a b c = admit()

val gte_mask_logand_lemma: a:uint64 -> b:uint64 -> c:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (c `logand` (gte_mask a b)) == v c
    else
      v (c `logand` (gte_mask a b)) == 0))
  [SMTPat (c `logand` (gte_mask a b))]
let gte_mask_logand_lemma a b c = admit()

val eq_mask_lemma: a:uint64 -> b:uint64 ->
  Lemma
  (requires True)
  (ensures
  (if v a = v b then
    v (eq_mask a b) == pow2 64 - 1
  else
    v (eq_mask a b) == 0))
  [SMTPat (eq_mask a b)]
let eq_mask_lemma a b = admit()

val gte_mask_lemma: a:uint64 -> b:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (gte_mask a b) == pow2 64 - 1
    else
      v (gte_mask a b) == 0))
  [SMTPat (gte_mask a b)]
let gte_mask_lemma a b = admit()

val logand_lemma: a:uint64 -> b:uint64 ->
  Lemma
  (requires v a = 0 \/ v a = pow2 64 - 1)
  (ensures
    (if v a = 0 then
      v (a `logand` b) == 0
    else
      v (a `logand` b) == v b))
  [SMTPat (a `logand` b)]
let logand_lemma a b = admit()
