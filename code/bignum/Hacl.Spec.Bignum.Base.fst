module Hacl.Spec.Bignum.Base

open FStar.Mul
open Lib.IntTypes

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let carry = x:uint64{uint_v x == 0 \/ uint_v x == 1}

(**
 This is non-stateful version of code/fallback functions
*)
inline_for_extraction noextract
val addcarry_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 64 == uint_v a + uint_v b + uint_v c)

let addcarry_u64 cin x y =
  let res = x +. cin +. y in
  let c = logand (logor (lt_mask res x) (logand (eq_mask res x) cin)) (u64 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (lt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (lt_mask res x) (logand (eq_mask res x) cin)) (u64 1) 1;
  c, res


inline_for_extraction noextract
val subborrow_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r - uint_v c' * pow2 64 == uint_v a - uint_v b - uint_v c)

let subborrow_u64 cin x y =
  let res = x -. y -. cin in
  let c = logand (logor (gt_mask res x) (logand (eq_mask res x) cin)) (u64 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (gt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (gt_mask res x) (logand (eq_mask res x) cin)) (u64 1) 1;
  c, res
