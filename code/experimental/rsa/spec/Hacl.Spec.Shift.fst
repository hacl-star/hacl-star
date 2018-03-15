module Hacl.Spec.Shift

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

let bn_tbit = u64 0x8000000000000000

val bn_lshift1_:
  aLen:size_nat{aLen > 0} ->
  a:lseqbn aLen -> carry:uint64 -> i:size_nat{i <= aLen} ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
  (decreases (aLen - i))
let rec bn_lshift1_ aLen a carry i res =
  if (i < aLen) then begin
    let tmp = a.[i] in
    let res = res.[i] <- (tmp <<. (u32 1)) |. carry in
    let carry = if (eq_u64 (tmp &. bn_tbit) bn_tbit) then u64 1 else u64 0 in
    bn_lshift1_ aLen a carry (i + 1) res
  end else res

// res = a << 1
val bn_lshift1:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_lshift1 aLen a res = bn_lshift1_ aLen a (u64 0) 0 res
