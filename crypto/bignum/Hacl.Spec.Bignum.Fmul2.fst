module Hacl.Spec.Bignum.Fmul2

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul.Lemmas
open Hacl.Spec.Bignum.Fmul

module U32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0"

val fmul_spec:
  input:seqelem -> input2:seqelem{fmul_pre input input2} ->
  Tot (output:seqelem{seval output % prime = (seval input * seval input2) % prime})
let fmul_spec input input2 =
  lemma_mul_to_red input input2;
  let tmp = Seq.create len wide_zero in
  let output1 = mul_shift_reduce_spec input input2 in
  let output2 = carry_wide_spec output1 0 in
  lemma_carry_top_wide_spec output2;
  let output3 = carry_top_wide_spec output2 in
  lemma_copy_from_wide output3;
  let output4 = copy_from_wide_spec output3 in
  carry_0_to_1_spec output4

#set-options "--z3rlimit 40"


val lemma_whole_slice: #a:Type -> s:Seq.seq a -> Lemma
  (Seq.slice s 0 (Seq.length s) == s)
let lemma_whole_slice #a s = Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s
