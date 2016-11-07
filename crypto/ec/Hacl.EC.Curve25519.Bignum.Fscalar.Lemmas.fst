module Hacl.EC.Curve25519.Bignum.Fscalar.Lemmas

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum.Lemmas.Utils

module U32 = FStar.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

#reset-options "--initial_fuel 0 --max_fuel 0"

let willNotOverflow (h:heap) (a:bigint) (s:s64) : GTot Type0 =
  live h a /\ v (get h a 0) * v s < pow2 128 /\ v (get h a 1) * v s < pow2 128
  /\ v (get h a 2) * v s < pow2 128 /\ v (get h a 3) * v s < pow2 128 /\ v (get h a 4) * v s < pow2 128


let isScalarMult h0 h1 (res:bigint_wide) (a:bigint) (s:s64) : GTot Type0 =
  live h0 a /\ live h1 res
  /\ H128.v (get h1 res 0) = v (get h0 a 0) * v s
  /\ H128.v (get h1 res 1) = v (get h0 a 1) * v s
  /\ H128.v (get h1 res 2) = v (get h0 a 2) * v s
  /\ H128.v (get h1 res 3) = v (get h0 a 3) * v s
  /\ H128.v (get h1 res 4) = v (get h0 a 4) * v s


let bound115 h (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h b
  /\ v (get h b 0) < pow2 115
  /\ v (get h b 1) < pow2 115
  /\ v (get h b 2) < pow2 115
  /\ v (get h b 3) < pow2 115
  /\ v (get h b 4) < pow2 115


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_fscalar:
  h0:mem -> h1:mem ->
  res:bigint_wide ->
  a:bigint ->
  s:s64 ->
  Lemma (requires (isScalarMult h0 h1 res a s /\ norm h0 a))
        (ensures  (isScalarMult h0 h1 res a s /\ norm h0 a
          /\ bound115 h1 res
          /\ eval_wide h1 res norm_length = eval h0 a norm_length * v s))
let lemma_fscalar h0 h1 res a s =
  assert_norm(pow2 115 = 41538374868278621028243970633760768);
  assert_norm(pow2 64 = 18446744073709551616);
  assert_norm(pow2 51 = 2251799813685248);
  Math.Lemmas.lemma_mult_le_right (v s) (v (get h0 a 0)) (pow2 51 - 1);
  Math.Lemmas.lemma_mult_le_right (v s) (v (get h0 a 1)) (pow2 51 - 1);
  Math.Lemmas.lemma_mult_le_right (v s) (v (get h0 a 2)) (pow2 51 - 1);
  Math.Lemmas.lemma_mult_le_right (v s) (v (get h0 a 3)) (pow2 51 - 1);
  Math.Lemmas.lemma_mult_le_right (v s) (v (get h0 a 4)) (pow2 51 - 1);
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_wide_5 h1 res;
  cut (eval_wide h1 res norm_length =
    (v (get h0 a 0) * v s) + pow2 51 * (v (get h0 a 1) * v s) + pow2 102 * (v (get h0 a 2) * v s) +
      pow2 153 * (v (get h0 a 3) * v s) + pow2 204 * (v (get h0 a 4) * v s));
  Math.Lemmas.paren_mul_right (pow2 51) (v (get h0 a 1)) (v s);
  Math.Lemmas.paren_mul_right (pow2 102) (v (get h0 a 2)) (v s);
  Math.Lemmas.paren_mul_right (pow2 153) (v (get h0 a 3)) (v s);
  Math.Lemmas.paren_mul_right (pow2 204) (v (get h0 a 4)) (v s);
  Math.Lemmas.distributivity_add_left (v (get h0 a 0)) (pow2 51 * v (get h0 a 1)) (v s);
  Math.Lemmas.distributivity_add_left (v (get h0 a 0) + pow2 51 * v (get h0 a 1))
                                      (pow2 102 * v (get h0 a 2)) (v s);
  Math.Lemmas.distributivity_add_left (v (get h0 a 0) + pow2 51 * v (get h0 a 1) + pow2 102 * v (get h0 a 2)) (pow2 153 * v (get h0 a 3)) (v s);
  Math.Lemmas.distributivity_add_left (v (get h0 a 0) + pow2 51 * v (get h0 a 1) + pow2 102 * v (get h0 a 2) + pow2 153 * v (get h0 a 3)) (pow2 204 * v (get h0 a 4)) (v s)
