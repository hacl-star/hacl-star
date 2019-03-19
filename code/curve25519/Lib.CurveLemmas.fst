module Lib.CurveLemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module BSeq = Lib.ByteSequence

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

val logor_disjoint64: a:uint64 -> b:uint64 -> m:pos{m < 64}
  -> Lemma
    (requires v a < pow2 m /\ v b % pow2 m == 0)
    (ensures v (a `logor` b) == v a + v b)
let logor_disjoint64 a b m = admit()

val lemma_nat_from_uints64_le_4: b:lseq uint64 4 ->
  Lemma (BSeq.nat_from_intseq_le b ==
    v b.[0] + v b.[1] * pow2 64 +
    v b.[2] * pow2 64 * pow2 64 + v b.[3] * pow2 64 * pow2 64 * pow2 64)
let lemma_nat_from_uints64_le_4 b = admit()

val logxor_lemma: a:uint64 -> b:uint64 ->
  Lemma (a ^. (a ^. b) == b /\ a ^. (b ^. a) == b /\ a ^. u64 0 == a)
let logxor_lemma a b = admit()

val logxor_lemma1: a:uint64 -> b:uint64
  -> Lemma
    (requires v a <= 1 /\ v b <= 1)
    (ensures v (a ^. b) <= 1)
let logxor_lemma1 a b = admit()
