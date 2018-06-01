module Spec.Bignum.Base

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

val eq_u8: a:uint8 -> b:uint8 -> Tot bool
let eq_u8 a b = FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

val lt_u64: a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

val le_u64: a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b = FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

let addcarry_u64 a b c =
  let c = to_u64 c in
  let t1 = add_mod #U64 a c in
  let c = if (lt_u64 t1 c) then u64 1 else u64 0 in
  let res = add_mod #U64 t1 b in
  let c = if (lt_u64 res t1) then add #U64 c (u64 1) else c in
  let c = to_u8 c in
  (c, res)

let subborrow_u64 a b c =
  let res = sub_mod #U64 (sub_mod #U64 a b) (to_u64 c) in
  let c =
    if (eq_u8 c (u8 1)) then
      (if (le_u64 a b) then u8 1 else u8 0)
    else
      (if (lt_u64 a b) then u8 1 else u8 0) in
  (c, res)

let mul_carry_add_u64 a b c d =
  assume (uint_v #U64 a * uint_v #U64 b + uint_v #U64 c + uint_v #U64 d < pow2 128);
  let res = add #U128 (add #U128 (mul_wide a b) (to_u128 #U64 c)) (to_u128 #U64 d) in
  let r = to_u64 res in
  let c' = to_u64 (res >>. u32 64) in
  (c', r)

(*
val add_with_carry:
  a:uint64 -> b:uint64 -> c:carry -> Pure (tuple2 carry uint64)
  (requires (True))
  (ensures (fun (c', r) -> uint_v r + uint_v c' * x_i 1 = uint_v a + uint_v b + uint_v c))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let add_with_carry a b c =
  let tmp = to_u128 a +! to_u128 b +! to_u128 c in
  let r = to_u64 tmp in
  assert (uint_v r = (uint_v a + uint_v b + uint_v c) % pow2 64);
  let c' = to_u8 (tmp >>. (u32 64)) in
  assert (uint_v c' = (uint_v a + uint_v b + uint_v c) / pow2 64);
  lemma_div_mod (uint_v a + uint_v b + uint_v c) (pow2 64);
  assert_norm (x_i 1 = pow2 64);
  assert (uint_v c' == 0 \/ uint_v c' == 1);
  (c', r)
*)
