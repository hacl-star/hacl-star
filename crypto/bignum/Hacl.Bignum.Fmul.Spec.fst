module Hacl.Bignum.Fmul.Spec

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo.Spec
open Hacl.Bignum.Fproduct.Spec

module U32 = FStar.UInt32


let shift_reduce_pre (s:seqelem) : GTot Type0 = reduce_pre (shift_spec s)


val shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Tot (s':seqelem)
let shift_reduce_spec s =
  reduce_spec (shift_spec s)


let rec mul_shift_reduce_pre (output:seqelem_wide) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  if ctr > 0 then (
    sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-ctr)) len
    /\ (let output' = sum_scalar_multiplication_spec output input (Seq.index input2 (len-ctr)) len in
       (ctr > 1 ==> shift_reduce_pre input) /\
         (let input'  = if ctr > 1 then shift_reduce_spec input else input in
          mul_shift_reduce_pre output' input' input2 (ctr-1))))
          else true


val mul_shift_reduce_spec:
  output:seqelem_wide ->
  input:seqelem -> input2:seqelem ->
  ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr} ->
  Tot seqelem_wide
  (decreases ctr)
let rec mul_shift_reduce_spec output input input2 ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let j = len - i - 1 in
    let input2j = Seq.index input2 j in
    let output' = sum_scalar_multiplication_spec output input input2j len in
    let input'  = if ctr > 1 then shift_reduce_spec input else input in
    mul_shift_reduce_spec output' input' input2 i
  )


let fmul_pre (input:seqelem) (input2:seqelem) : GTot Type0 =
  mul_shift_reduce_pre (Seq.create len wide_zero) input input2 len
