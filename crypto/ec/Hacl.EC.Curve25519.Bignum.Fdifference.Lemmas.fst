module Hacl.EC.Curve25519.Bignum.Fdifference.Lemmas

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

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

let addedZero h0 h1 (b:bigint) : GTot Type0 =
  norm h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) + (pow2 52 - 38)
  /\ v (get h1 b 1) = v (get h0 b 1) + (pow2 52 - 2)
  /\ v (get h1 b 2) = v (get h0 b 2) + (pow2 52 - 2)
  /\ v (get h1 b 3) = v (get h0 b 3) + (pow2 52 - 2)
  /\ v (get h1 b 4) = v (get h0 b 4) + (pow2 52 - 2)

val lemma_pow2_52m38: unit -> Lemma (0xfffffffffffda = pow2 52 - 38)
let lemma_pow2_52m38 () = assert_norm(0xfffffffffffda = pow2 52 - 38)

val lemma_pow2_52m2: unit -> Lemma (0xffffffffffffe = pow2 52 - 2)
let lemma_pow2_52m2 () = assert_norm(0xffffffffffffe = pow2 52 - 2)

val lemma_add_big_zero_core:
  b0:H64.t -> b1:H64.t -> b2:H64.t -> b3:H64.t -> b4:H64.t ->
  Lemma
    (requires (v b0 < pow2 51 /\ v b1 < pow2 51 /\ v b2 < pow2 51 /\ v b3 < pow2 51 /\ v b4 < pow2 51))
    (ensures  (v b0 + pow2 52 - 38 < pow2 64
      /\ v b1 + pow2 52 - 2 < pow2 64
      /\ v b2 + pow2 52 - 2 < pow2 64
      /\ v b3 + pow2 52 - 2 < pow2 64
      /\ v b4 + pow2 52 - 2 < pow2 64))
let lemma_add_big_zero_core b0 b1 b2 b3 b4 =
  assert_norm(pow2 1 = 2);
  pow2_lt_compat 52 1;
  pow2_double_sum 51;
  pow2_double_sum 52;
  pow2_lt_compat 64 53

let bound53 h (b:bigint) : GTot Type0 =
  live h b
  /\ v (get h b 0) < pow2 53
  /\ v (get h b 1) < pow2 53
  /\ v (get h b 2) < pow2 53
  /\ v (get h b 3) < pow2 53
  /\ v (get h b 4) < pow2 53

let fits51to53 h (b:bigint) : GTot Type0 =
  bound53 h b
  /\ v (get h b 0) >= pow2 51
  /\ v (get h b 1) >= pow2 51
  /\ v (get h b 2) >= pow2 51
  /\ v (get h b 3) >= pow2 51
  /\ v (get h b 4) >= pow2 51

let isDifference h0 h1 a b =
  fits51to53 h0 b /\ norm h0 a /\ live h1 a
  /\ v (get h1 a 0) = v (get h0 b 0) - v (get h0 a 0)
  /\ v (get h1 a 1) = v (get h0 b 1) - v (get h0 a 1)
  /\ v (get h1 a 2) = v (get h0 b 2) - v (get h0 a 2)
  /\ v (get h1 a 3) = v (get h0 b 3) - v (get h0 a 3)
  /\ v (get h1 a 4) = v (get h0 b 4) - v (get h0 a 4)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val lemma_add_zero_eval_:
  h0:mem -> h1:mem ->
  b:bigint{addedZero h0 h1 b} ->
  Lemma (requires (True))
        (ensures  (fits51to53 h1 b))
let lemma_add_zero_eval_ h0 h1 b =
  assert_norm(9007199254740992 = pow2 53);
  assert_norm(pow2 52 = 4503599627370496);
  assert_norm(2251799813685248 = pow2 51)


val lemma_add_zero_eval:
  h0:mem -> h1:mem ->
  b:bigint{addedZero h0 h1 b} ->
  Lemma (requires (True))
        (ensures  (eval h1 b 5 % reveal prime = eval h0 b 5 % reveal prime
          /\ fits51to53 h1 b))
let lemma_add_zero_eval h0 h1 b =
  lemma_add_zero_eval_ h0 h1 b;
  lemma_eval_bigint_5 h1 b;
  lemma_eval_bigint_5 h0 b;
  let e = eval h1 b 5 in
  cut (e = v (get h1 b 0) + pow2 51 * v (get h1 b 1) + pow2 102 * v (get h1 b 2)
           + pow2 153 * v (get h1 b 3) + pow2 204 * v (get h1 b 4));
  Math.Lemmas.distributivity_add_right (pow2 51) (v (get h0 b 1)) (pow2 52 - 2);
  Math.Lemmas.distributivity_add_right (pow2 102) (v (get h0 b 2)) (pow2 52 - 2);
  Math.Lemmas.distributivity_add_right (pow2 153) (v (get h0 b 3)) (pow2 52 - 2);
  Math.Lemmas.distributivity_add_right (pow2 204) (v (get h0 b 4)) (pow2 52 - 2);
  cut (eval h1 b 5 = eval h0 b 5 + (pow2 52 - 38) + pow2 51 * (pow2 52 - 2)
                     + pow2 102 * (pow2 52 - 2)  + pow2 153 * (pow2 52 - 2)
                     + pow2 204 * (pow2 52 - 2));
  assert_norm ((pow2 52 - 38) + pow2 51 * (pow2 52 - 2)
                     + pow2 102 * (pow2 52 - 2)  + pow2 153 * (pow2 52 - 2)
                     + pow2 204 * (pow2 52 - 2) = 2 * (pow2 255 - 19));
  cut (eval h1 b 5 = eval h0 b 5 + 2 * (pow2 255 - 19));
  assert_norm (pow2 255 - 19 > 0);
  cut (pow2 255 - 19 = reveal prime);
  Math.Lemmas.lemma_mod_plus (eval h0 b 5) 2 (pow2 255 - 19)

val factorization_lemma: unit ->
  Lemma (requires (True))
	(ensures  (forall a b c. {:pattern (a * (b-c))} a * (b - c) = a * b - a * c))
let factorization_lemma () = ()

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_fdifference: h0:mem -> h1:mem -> a:bigint -> b:bigint -> Lemma
  (requires (norm h0 a /\ fits51to53 h0 b /\ isDifference h0 h1 a b))
  (ensures  (norm h0 a /\ fits51to53 h0 b /\ isDifference h0 h1 a b
    /\ bound53 h1 a
    /\ eval h1 a norm_length = eval h0 b norm_length - eval h0 a norm_length))
let lemma_fdifference h0 h1 a b =
  assert_norm(9007199254740992 = pow2 53);
  assert_norm(pow2 52 = 4503599627370496);
  assert_norm(2251799813685248 = pow2 51);
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_5 h0 b;
  factorization_lemma ();
  lemma_eval_bigint_5 h1 a
