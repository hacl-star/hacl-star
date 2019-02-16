module Hacl.Helpers

open Lib.IntTypes

let uint64_eq_mask (a:uint64) (b:uint64) : uint64 =
  let x = a ^. b in
  let minus_x = (lognot x) +. (u64 1) in
  let x_or_minus_x = x |. minus_x in
  let xnx = x_or_minus_x >>. 63ul in
  let c = xnx -. (u64 1) in
  c

let uint64_gte_mask (a:uint64) (b:uint64) : uint64 =
  let x = a in
  let y = b in
  let x_xor_y = logxor x y in
  let x_sub_y = x -. y in
  let x_sub_y_xor_y = x_sub_y ^. y in
  let q = logor x_xor_y x_sub_y_xor_y in
  let x_xor_q = logxor x q in
  let x_xor_q_ = shift_right x_xor_q 63ul in
  let c = sub_mod x_xor_q_ (u64 1) in
  c

val uint64_eq_mask_logand_lemma: a:uint64 -> b:uint64 -> c:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a = v b then
      v (c `logand` (uint64_eq_mask a b)) == v c
    else
      v (c `logand` (uint64_eq_mask a b)) == 0))
  [SMTPat (c `logand` (uint64_eq_mask a b))]
let uint64_eq_mask_logand_lemma a b c = admit()

val uint64_gte_mask_logand_lemma: a:uint64 -> b:uint64 -> c:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (c `logand` (uint64_gte_mask a b)) == v c
    else
      v (c `logand` (uint64_gte_mask a b)) == 0))
  [SMTPat (c `logand` (uint64_gte_mask a b))]
let uint64_gte_mask_logand_lemma a b c = admit()

val uint64_eq_mask_lemma: a:uint64 -> b:uint64 ->
  Lemma
  (requires True)
  (ensures
  (if v a = v b then
    v (uint64_eq_mask a b) == pow2 64 - 1
  else
    v (uint64_eq_mask a b) == 0))
  [SMTPat (uint64_eq_mask a b)]
let uint64_eq_mask_lemma a b = admit()

val uint64_gte_mask_lemma: a:uint64 -> b:uint64 ->
  Lemma
  (requires True)
  (ensures
    (if v a >= v b then
      v (uint64_gte_mask a b) == pow2 64 - 1
    else
      v (uint64_gte_mask a b) == 0))
  [SMTPat (uint64_gte_mask a b)]
let uint64_gte_mask_lemma a b = admit()

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
