module Hacl.Spec.Lib

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas

type lseqbn len = intseq U64 len

val bval: bLen:size_nat{bLen > 0} -> b:lseqbn bLen -> i:size_nat -> Tot uint64
let bval bLen b i = if (i < bLen) then b.[i] else u64 0

val eq_u64: a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b = FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

val lt_u64: a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

val le_u64: a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b = FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

val bn_is_bit_set:
  len:size_nat ->
  input:lseqbn len ->
  ind:size_nat{ind / 64 < len} -> Tot bool
let bn_is_bit_set len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  let tmp = (tmp >>. u32 j) &. u64 1 in
  eq_u64 tmp (u64 1)

val bn_set_bit:
  len:size_nat ->
  input:lseqbn len ->
  ind:size_nat{ind / 64 < len} -> Tot (lseqbn len)
let bn_set_bit len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  input.[i] <- (tmp |. ((u64 1) <<. u32 j))
