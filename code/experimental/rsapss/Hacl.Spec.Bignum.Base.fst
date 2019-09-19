module Hacl.Spec.Bignum.Base

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let carry = x:uint64{uint_v x == 0 \/ uint_v x == 1}

inline_for_extraction noextract
val eq_u64: a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

inline_for_extraction noextract
val lt_u64: a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64: a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)


inline_for_extraction noextract
val addcarry_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 64 == uint_v a + uint_v b + uint_v c)

let addcarry_u64 c a b =
  let t1 = a +. c in
  let c = if lt_u64 t1 c then u64 1 else u64 0 in
  let res = t1 +. b in
  let c = if lt_u64 res t1 then c +. u64 1 else c in
  c, res


inline_for_extraction noextract
val subborrow_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r - uint_v c' * pow2 64 == uint_v a - uint_v b - uint_v c)

let subborrow_u64 c a b =
  let res = a -. b -. c in
  let c =
    if eq_u64 c (u64 1) then
      (if le_u64 a b then u64 1 else u64 0)
    else
      (if lt_u64 a b then u64 1 else u64 0) in
  c, res


val lemma_mul_carry_add_64: a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 ->
  Lemma (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128)
let lemma_mul_carry_add_64 a b c d =
  let n = pow2 64 in
  assert (uint_v a <= n - 1 /\ uint_v b <= n - 1 /\ uint_v c <= n - 1 /\ uint_v d <= n - 1);
  assert (uint_v a * uint_v b + uint_v c + uint_v d <= (n - 1) * (n - 1) + (n - 1) + (n - 1));
  assert ((n - 1) * (n - 1) + (n - 1) + (n - 1) == n * n - 1);
  FStar.Math.Lemmas.pow2_plus 64 64


#set-options "--z3rlimit 100"

inline_for_extraction noextract
val mul_carry_add_u64: a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 ->
  Pure (tuple2 uint64 uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 64 == uint_v a * uint_v b + uint_v c + uint_v d)

let mul_carry_add_u64 a b c d =
  lemma_mul_carry_add_64 a b c d;
  assert (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128);
  let res = mul64_wide a b +! to_u128 #U64 c +! to_u128 #U64 d in
  let r = to_u64 res in
  let c' = to_u64 (res >>. 64ul) in
  c', r
