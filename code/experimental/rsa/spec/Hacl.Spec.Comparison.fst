module Hacl.Spec.Comparison

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

val bn_is_less_:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  i:size_nat{i <= aLen} -> Tot bool
let rec bn_is_less_ aLen a bLen b i =
  if (i > 0) then
    let i = i - 1 in
    let t1 = a.[i] in
    let t2 = bval bLen b i in
    (if not (eq_u64 t1 t2) then
      if lt_u64 t1 t2 then true else false
    else bn_is_less_ aLen a bLen b i)
  else false

val bn_is_less:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen -> Tot bool
let bn_is_less aLen a bLen b = bn_is_less_ aLen a bLen b aLen
