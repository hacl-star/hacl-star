module Hacl.EC.AddAndDouble

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Fsum
open Hacl.Spec.Bignum.Fdifference
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fmul
open Hacl.EC.Point


val bound_by: seqelem -> nat -> Type0
let bound_by s x =
  let _ = () in
  (forall (i:nat). {:pattern (v (Seq.index s i))} i < len ==> v (Seq.index s i) < x)


val smax: seqelem -> nat -> Type0
let smax s x =
  let _ = () in
  v (Seq.index s 0) < x /\ v (Seq.index s 1) < x /\ v (Seq.index s 2) < x
  /\ v (Seq.index s 3) < x /\ v (Seq.index s 4) < x


let red_52 s = smax s 52
let red_53 s = smax s 53
let red_55 s = smax s 55


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private val mul_shift_reduce_unrolled_0:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 1} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 1})
private let mul_shift_reduce_unrolled_0 output input_init input input2 =
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 4) len in
  output1


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private val mul_shift_reduce_unrolled_1:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 2} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 2})
private let mul_shift_reduce_unrolled_1 output input_init input input2 =
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 3) len in
  lemma_sum_scalar_multiplication_ output input (Seq.index input2 3) len;
  let input1    = shift_reduce_spec input in
  lemma_shift_reduce_spec input;
  lemma_mul_shift_reduce_spec_1 output1 output input_init input input1 input2 (v (Seq.index input2 3)) 2;
  mul_shift_reduce_unrolled_0 output1 input_init input1 input2


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private val mul_shift_reduce_unrolled_2:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 3} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 3})
private let mul_shift_reduce_unrolled_2 output input_init input input2 =
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 2) len in
  lemma_sum_scalar_multiplication_ output input (Seq.index input2 2) len;
  let input1    = shift_reduce_spec input in
  lemma_shift_reduce_spec input;
  lemma_mul_shift_reduce_spec_1 output1 output input_init input input1 input2 (v (Seq.index input2 2)) 3;
  mul_shift_reduce_unrolled_1 output1 input_init input1 input2


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private val mul_shift_reduce_unrolled_3:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 4} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 4})
private let mul_shift_reduce_unrolled_3 output input_init input input2 =
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 1) len in
  lemma_sum_scalar_multiplication_ output input (Seq.index input2 1) len;
  let input1    = shift_reduce_spec input in
  lemma_shift_reduce_spec input;
  lemma_mul_shift_reduce_spec_1 output1 output input_init input input1 input2 (v (Seq.index input2 1)) 4;
  mul_shift_reduce_unrolled_2 output1 input_init input1 input2


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private val mul_shift_reduce_unrolled_:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 5} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 5})
private let mul_shift_reduce_unrolled_ output input_init input input2 =
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 0) len in
  lemma_sum_scalar_multiplication_ output input (Seq.index input2 0) len;
  let input1    = shift_reduce_spec input in
  lemma_shift_reduce_spec input;
  lemma_mul_shift_reduce_spec_1 output1 output input_init input input1 input2 (v (Seq.index input2 0)) 5;
  mul_shift_reduce_unrolled_3 output1 input_init input1 input2


private val shift_reduce_unrolled:
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec input input2})
private let shift_reduce_unrolled input input2 =
  mul_shift_reduce_unrolled_ (Seq.create len wide_zero) input input input2


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} ->
  Tot (s':seqelem_wide{w (Seq.index s' 4) < w (Seq.index s 4) + pow2 (2*word_size-limb_size)})
private let carry_wide_spec_unrolled s =
  let s1 = carry_wide_step s 0 in
  lemma_carry_wide_step s 0;
  let s2 = carry_wide_step s1 1 in
  lemma_carry_wide_step s1 1;
  let s3 = carry_wide_step s2 2 in
  lemma_carry_wide_step s2 2;
  let s4 = carry_wide_step s3 3 in
  lemma_carry_wide_step s3 3;
  Math.Lemmas.lemma_div_lt (w (Seq.index s3 3)) (2*word_size) limb_size;
  cut (w (Seq.index s4 4) < w (Seq.index s 4) + pow2 (2*word_size - limb_size));
  s4


#set-options "--z3rlimit 20 --initial_fuel 5 --max_fuel 5"

private val lemma_carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} -> Lemma (carry_wide_spec_unrolled s == carry_wide_spec s 0)
let lemma_carry_wide_spec_unrolled s = ()


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_copy_then_carry: s:seqelem_wide -> Lemma
  ((copy_from_wide_pre s /\ (w (Seq.index s 0) < pow2 word_size /\ w (Seq.index s 1) < pow2 limb_size
    /\ w (Seq.index s 2) < pow2 limb_size /\ w (Seq.index s 3) < pow2 limb_size
    /\ w (Seq.index s 4) < pow2 limb_size)) ==>
     (carry_0_to_1_pre (copy_from_wide_spec s) ))
let lemma_copy_then_carry s = ()



val lemma_carry_top_wide_then_copy: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  ((w (Seq.index s 0) + 19 * w (Seq.index s 4) / pow2 limb_size < pow2 word_size /\ w (Seq.index s 1) < pow2 word_size /\ w (Seq.index s 2) < pow2 word_size /\ w (Seq.index s 3) < pow2 word_size) ==> copy_from_wide_pre (carry_top_wide_spec s))
let lemma_carry_top_wide_then_copy s =
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 64 > pow2 51)

#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val lemma_carry_wide_then_carry_top: s:seqelem_wide{carry_wide_pre s 0} -> Lemma
  (((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 limb_size < pow2 word_size
    /\ 19 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 limb_size) + pow2 limb_size < pow2 word_size)
    ==> carry_top_wide_pre (carry_wide_spec s 0) )
let lemma_carry_wide_then_carry_top s =
  let s' = carry_wide_spec_unrolled s in
  lemma_carry_wide_spec_unrolled s;
  cut (w (Seq.index s' 4) < w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 19 (w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  if ((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 limb_size < pow2 word_size
    && 19 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 limb_size) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (w (Seq.index s' 4)) (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) (pow2 limb_size);
    cut (w (Seq.index s' 4) / pow2 limb_size <= (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 limb_size);
    Math.Lemmas.nat_over_pos_is_nat (w (Seq.index s' 4)) (pow2 limb_size);
    Math.Lemmas.nat_over_pos_is_nat (((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 limb_size)) (pow2 limb_size);
    Math.Lemmas.multiplication_order_lemma (w (Seq.index s' 4) / pow2 limb_size)
                                           ((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 limb_size) 19;
    cut (19 * (w (Seq.index s' 4) / pow2 limb_size) <= 19 * ((w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 limb_size));
    cut (w (Seq.index s' 0) < pow2 limb_size);
    cut (19 * (w (Seq.index s' 4) / pow2 limb_size) + w (Seq.index s' 0) < pow2 word_size);
    Math.Lemmas.pow2_lt_compat (2*word_size) word_size
  )
  else ()
