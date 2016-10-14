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
