module Hacl.Spec.Bignum.Fmul.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul

module U32 = FStar.UInt32

val lemma_mul_to_red: input:seqelem -> input2:seqelem -> Lemma
  (requires (fmul_pre input input2))
  (ensures  (fmul_pre input input2
    /\ carry_wide_pre (mul_shift_reduce_spec input input2) 0
    /\ carry_top_wide_pre (carry_wide_spec (mul_shift_reduce_spec input input2) 0)
    /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (mul_shift_reduce_spec input input2) 0))
    /\ carry_0_to_1_pre (copy_from_wide_spec (carry_top_wide_spec (carry_wide_spec (mul_shift_reduce_spec input input2) 0)))))
