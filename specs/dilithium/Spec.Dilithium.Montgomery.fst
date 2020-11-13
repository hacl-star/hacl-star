module Spec.Dilithium.Montgomery

open Spec.Dilithium.Params

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

let mont = // 2^32 % Q
  let mont = 4193792 in
  assert_norm (mont % param_q = (pow2 32) % param_q);
  mont

let qinv = // -q^(-1) mod 2^32
  let qinv = 4236238847 in
  assert_norm ((qinv * param_q + 1) % (pow2 32) = 0);
  qinv


// precondition a < q * pow2 32 maybe?
let montgomery_reduce (a:uint64) : uint32 =
  let t = a *. u64 qinv in
  let t = t &. ((u64 1) <<. size 32) -. u64 1 in
  let t = t *. u64 param_q in
  let t = a +. t in
  to_u32 (t >>. size 32)

let reduce32 (a:uint32) =
  let t = a &. u32 0x7FFFFF in
  let a = a >>. size 23 in
  t +. (a <<. size 13) -. a


let csubq (a:uint32) =
  if v a > param_q then a -. u32 param_q else a


let freeze (a:uint32) =
  let a = reduce32 a in
  csubq a