module Hacl.Spec.Bignum.Multiplication

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_mul_by_limb_addj_f:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> res:lbignum aLen
  -> i:size_nat{i < aLen}
  -> c:uint64 ->
  uint64 & uint64 // carry & out

let bn_mul_by_limb_addj_f #aLen a l res i c =
  mul_carry_add_u64 a.[i] l c res.[i]


val bn_mul_by_limb_addj:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> res:lbignum aLen ->
  uint64 & lbignum aLen

let bn_mul_by_limb_addj #aLen a l res =
  generate_elems aLen aLen (bn_mul_by_limb_addj_f a l res) (u64 0)


val bn_mul_:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> j:size_nat{j < bLen}
  -> res:lbignum (aLen + bLen) ->
  lbignum (aLen + bLen)

let bn_mul_ #aLen #bLen a b j res =
  let res' = sub res j aLen in
  let c, res' = bn_mul_by_limb_addj #aLen a b.[j] res' in
  let res = update_sub res j aLen res' in
  res.[aLen + j] <- c


val bn_mul:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  lbignum (aLen + bLen)

let bn_mul #aLen #bLen a b =
  let res = create (aLen + bLen) (u64 0) in
  repeati bLen (bn_mul_ #aLen #bLen a b) res
