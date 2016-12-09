module Hacl.EC.Curve25519.Bignum.Lemmas.Utils

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_bitweight_values: unit ->
  Lemma (bitweight templ 0 = 0 /\ bitweight templ 1 = 51
	/\ bitweight templ 2 = 102 /\ bitweight templ 3 = 153
	/\ bitweight templ 4 = 204 /\ bitweight templ 5 = 255
	/\ bitweight templ 6 = 306 /\ bitweight templ 7 = 357
	/\ bitweight templ 8 = 408 /\ bitweight templ 9 = 459)
let lemma_bitweight_values () =
  bitweight_def templ 0;
  bitweight_def templ 1;
  bitweight_def templ 2;
  bitweight_def templ 3;
  bitweight_def templ 4;
  bitweight_def templ 5;
  bitweight_def templ 6;
  bitweight_def templ 7;
  bitweight_def templ 8;
  bitweight_def templ 9


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_5:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b))
	(ensures  (live h b
	  /\ eval h b norm_length = v (get h b 0) + pow2 51  * v (get h b 1)
						  + pow2 102 * v (get h b 2)
						  + pow2 153 * v (get h b 3)
						  + pow2 204 * v (get h b 4) ))
let lemma_eval_bigint_5 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_6:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b /\ length b >= norm_length+1))
	(ensures  (live h b /\ length b >= norm_length+1
	  /\ eval h b (norm_length+1) = v (get h b 0) + pow2 51  * v (get h b 1)
						     + pow2 102  * v (get h b 2)
						     + pow2 153  * v (get h b 3)
						     + pow2 204 * v (get h b 4)
						     + pow2 255 * v (get h b 5) ))
let lemma_eval_bigint_6 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5;
  eval_def h b 6

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_9:
  h:mem ->
  b:bigint ->
  Lemma (requires (live h b /\ length b >= 2*norm_length-1))
	(ensures  (live h b /\ length b >= 2*norm_length-1
	  /\ eval h b (2*norm_length-1) = v (get h b 0) + pow2 51  * v (get h b 1)
						       + pow2 102  * v (get h b 2)
						       + pow2 153  * v (get h b 3)
						       + pow2 204 * v (get h b 4)
						       + pow2 255 * v (get h b 5)
						       + pow2 306 * v (get h b 6)
						       + pow2 357 * v (get h b 7)
						       + pow2 408 * v (get h b 8) ))
let lemma_eval_bigint_9 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_def h b 0;
  eval_def h b 1;
  eval_def h b 2;
  eval_def h b 3;
  eval_def h b 4;
  eval_def h b 5;
  eval_def h b 6;
  eval_def h b 7;
  eval_def h b 8;
  eval_def h b 9

module H128 = Hacl.UInt128

val lemma_eval_bigint_wide_5:
  h:mem ->
  b:bigint_wide ->
  Lemma (requires (live h b))
	(ensures  (live h b
	  /\ eval_wide h b norm_length = H128.(v (get h b 0) + pow2 51  * v (get h b 1)
						  + pow2 102 * v (get h b 2)
						  + pow2 153 * v (get h b 3)
						  + pow2 204 * v (get h b 4)) ))
let lemma_eval_bigint_wide_5 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_wide_def h b 0;
  eval_wide_def h b 1;
  eval_wide_def h b 2;
  eval_wide_def h b 3;
  eval_wide_def h b 4;
  eval_wide_def h b 5


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_wide_6:
  h:mem ->
  b:bigint_wide ->
  Lemma (requires (live h b /\ length b >= norm_length+1))
	(ensures  (live h b /\ length b >= norm_length+1
	  /\ eval_wide h b (norm_length+1) = H128.(v (get h b 0) + pow2 51  * v (get h b 1)
						     + pow2 102  * v (get h b 2)
						     + pow2 153  * v (get h b 3)
						     + pow2 204 * v (get h b 4)
						     + pow2 255 * v (get h b 5)) ))
let lemma_eval_bigint_wide_6 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_wide_def h b 0;
  eval_wide_def h b 1;
  eval_wide_def h b 2;
  eval_wide_def h b 3;
  eval_wide_def h b 4;
  eval_wide_def h b 5;
  eval_wide_def h b 6

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_eval_bigint_wide_9:
  h:mem ->
  b:bigint_wide ->
  Lemma (requires (live h b /\ length b >= 2*norm_length-1))
	(ensures  (live h b /\ length b >= 2*norm_length-1
	  /\ eval_wide h b (2*norm_length-1) = H128.(v (get h b 0) + pow2 51  * v (get h b 1)
						       + pow2 102  * v (get h b 2)
						       + pow2 153  * v (get h b 3)
						       + pow2 204 * v (get h b 4)
						       + pow2 255 * v (get h b 5)
						       + pow2 306 * v (get h b 6)
						       + pow2 357 * v (get h b 7)
						       + pow2 408 * v (get h b 8)) ))
let lemma_eval_bigint_wide_9 h b =
  lemma_bitweight_values ();
  assert_norm (pow2 0 = 1);
  eval_wide_def h b 0;
  eval_wide_def h b 1;
  eval_wide_def h b 2;
  eval_wide_def h b 3;
  eval_wide_def h b 4;
  eval_wide_def h b 5;
  eval_wide_def h b 6;
  eval_wide_def h b 7;
  eval_wide_def h b 8;
  eval_wide_def h b 9
