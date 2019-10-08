module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Montgomery
open Hacl.Spec.Bignum.Montgomery.PreCompConstants


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_is_bit_set: #len:size_nat -> input:lbignum len -> ind:size_nat{ind / 64 < len} -> bool
let bn_is_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  let tmp = (tmp >>. size j) &. u64 1 in
  eq_u64 tmp (u64 1)


val mod_exp_f:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:nat{i < bBits}
  -> aM_accM: tuple2 (lbignum rLen) (lbignum rLen) ->
  tuple2 (lbignum rLen) (lbignum rLen)

let mod_exp_f #nLen #rLen n nInv_u64 bBits bLen b i aM_accM =
  let (aM, accM) = aM_accM in
  let accM = if (bn_is_bit_set #bLen b i) then mul_mod_mont n nInv_u64 aM accM else accM in // acc = (acc * a) % n
  let aM = mul_mod_mont n nInv_u64 aM aM in // a = (a * a) % n
  (aM, accM)


val mod_exp:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * (nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  res:lbignum nLen

let mod_exp modBits nLen n r2 a bBits b =
  let rLen = nLen + 1 in
  let bLen = blocks bBits 64 in

  let acc  = create nLen (u64 0) in
  let acc = acc.[0] <- u64 1 in
  let nInv_u64 = mod_inv_u64 n.[0] in

  let aM = to_mont n nInv_u64 r2 a in
  let accM = to_mont n nInv_u64 r2 acc in
  let (aM, accM) = repeati bBits (mod_exp_f #nLen #rLen n nInv_u64 bBits bLen b) (aM, accM) in
  from_mont n nInv_u64 accM
