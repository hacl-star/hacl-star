module Spec.Bignum.Base

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

let carry = x:uint8{uint_v x == 0 \/ uint_v x == 1}
let x_i (i:size_nat):nat = pow2 (64 * i)

val addcarry_u64:
  a:uint64 -> b:uint64 -> c:carry -> Pure (tuple2 carry uint64)
  (requires (True))
  (ensures (fun (c', r) -> uint_v r + uint_v c' * x_i 1 = uint_v a + uint_v b + uint_v c))

val subborrow_u64:
  a:uint64 -> b:uint64 -> c:carry -> Pure (tuple2 carry uint64)
  (requires (True))
  (ensures (fun (c', r) -> uint_v r - uint_v c' * x_i 1 = uint_v a - uint_v b - uint_v c))

val mul_carry_add_u64:
  a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 -> Pure (tuple2 uint64 uint64)
  (requires (True))
  (ensures (fun (c', r) -> uint_v r + uint_v c' * x_i 1 == uint_v a * uint_v b + uint_v c + uint_v d))
