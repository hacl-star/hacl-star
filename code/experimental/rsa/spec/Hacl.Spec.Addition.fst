module Hacl.Spec.Addition

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

type carry = uint64

val addcarry_u64: c:carry -> a:uint64 -> b:uint64 -> Tot (tuple2 carry uint64)
let addcarry_u64 c a b =
  let tmp = add #U128 (to_u128 #U64 c) (add #U128 (to_u128 #U64 a) (to_u128 #U64 b)) in
  let res = to_u64 tmp in
  let c' = to_u64 (tmp >>. u32 64) in
  (c', res)
  
val subborrow_u64: c:carry -> a:uint64 -> b:uint64 -> Tot (tuple2 carry uint64)
let subborrow_u64 c a b =
  let res = sub_mod #U64 (sub_mod #U64 a b) c in
  let c' =
    if eq_u64 c (u64 1)
    then (if le_u64 a b then u64 1 else u64 0)
    else (if lt_u64 a b then u64 1 else u64 0) in
  (c', res)

val bn_sub_:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  i:size_nat{i <= aLen} -> c:carry ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
  (decreases (aLen - i))
let rec bn_sub_ aLen a bLen b i c res =
  if (i < aLen) then begin
    let t2 = bval bLen b i in
    let (c', res_i) = subborrow_u64 c a.[i] t2 in
    let res' = res.[i] <- res_i in
    bn_sub_ aLen a bLen b (i + 1) c' res' end
  else res

val bn_sub:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_sub aLen a bLen b res =
  bn_sub_ aLen a bLen b 0 (u64 0) res

val bn_add_:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  i:size_nat{i <= aLen} -> c:carry ->
  res:lseqbn aLen -> Tot (tuple2 carry (lseqbn aLen))
  (decreases (aLen - i))
let rec bn_add_ aLen a bLen b i c res =
  if (i < aLen) then begin
    let t2 = bval bLen b i in
    let (c', res_i) = addcarry_u64 c a.[i] t2 in
    let res' = res.[i] <- res_i in
    bn_add_ aLen a bLen b (i + 1) c' res' end
  else (c, res)

val bn_add:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_add aLen a bLen b res =
  let (_, res) = bn_add_ aLen a bLen b 0 (u64 0) res in res

val bn_add_carry:
  aLen:size_nat{aLen + 1 < max_size_t} -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  res:lseqbn (aLen + 1) -> Tot (lseqbn (aLen + 1))
let bn_add_carry aLen a bLen b res =
  let res' = sub res 0 aLen in
  let (c', res') = bn_add_ aLen a bLen b 0 (u64 0) res' in
  let res = update_sub res 0 aLen res' in
  res.[aLen] <- c'

val bn_sub_u64_:
  aLen:size_nat{aLen > 0} ->
  a:lseqbn aLen -> carry:uint64 -> i:size_nat ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
  (decreases (aLen - i))
let rec bn_sub_u64_ aLen a carry i res =
  if (i < aLen) then begin
    let t1 = a.[i] in
    let res_i = t1 -. carry in
    let res = res.[i] <- res_i in
    let carry = if (lt_u64 t1 carry) then u64 1 else u64 0 in
    bn_sub_u64_ aLen a carry (i + 1) res
  end else res
    
val bn_sub_u64:
  aLen:size_nat{aLen > 0} ->
  a:lseqbn aLen -> b:uint64 ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_sub_u64 aLen a b res = bn_sub_u64_ aLen a b 0 res

