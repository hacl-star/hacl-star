module Lib.Lemmas

open Lib.IntTypes

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
