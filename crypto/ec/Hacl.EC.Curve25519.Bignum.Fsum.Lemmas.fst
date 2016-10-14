module Hacl.EC.Curve25519.Bignum.Fsum.Lemmas

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

#reset-options "--initial_fuel 0 --max_fuel 0"


let willNotOverflow (h:heap) (a:bigint) (b:bigint) : GTot Type0 =
  live h a /\ live h b /\ length a >= norm_length /\ length b >= norm_length
  /\ v (get h a 0) + v (get h b 0) < pow2 64
  /\ v (get h a 1) + v (get h b 1) < pow2 64
  /\ v (get h a 2) + v (get h b 2) < pow2 64
  /\ v (get h a 3) + v (get h b 3) < pow2 64
  /\ v (get h a 4) + v (get h b 4) < pow2 64

let isSum (h:heap) (h1:heap) (a:bigint) (b:bigint) : GTot Type0 =
  live h a /\ live h1 a /\ live h b /\ length a >= norm_length /\ length b >= norm_length
  /\ v (get h a 0) + v (get h b 0) = v (get h1 a 0)
  /\ v (get h a 1) + v (get h b 1) = v (get h1 a 1)
  /\ v (get h a 2) + v (get h b 2) = v (get h1 a 2)
  /\ v (get h a 3) + v (get h b 3) = v (get h1 a 3)
  /\ v (get h a 4) + v (get h b 4) = v (get h1 a 4)

let bound52 (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length
  /\ v (get h b 0) < pow2 52
  /\ v (get h b 1) < pow2 52
  /\ v (get h b 2) < pow2 52
  /\ v (get h b 3) < pow2 52
  /\ v (get h b 4) < pow2 52


let w : U32.t -> Tot int = U32.v

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_fsum_0:
  a0:H64.t -> a1:H64.t -> a2:H64.t -> a3:H64.t -> a4:H64.t ->
  b0:H64.t -> b1:H64.t -> b2:H64.t -> b3:H64.t -> b4:H64.t ->
  Lemma (requires (
	  v a0 < pow2 51 /\ v a1 < pow2 51 /\ v a2 < pow2 51 /\ v a3 < pow2 51 /\ v a4 < pow2 51
	  /\ v b0 < pow2 51 /\ v b1 < pow2 51 /\ v b2 < pow2 51 /\ v b3 < pow2 51 /\ v b4 < pow2 51))
	(ensures  (
		  v a0 + v b0 < pow2 64 /\ v a1 + v b1 < pow2 64 /\ v a2 + v b2 < pow2 64
		  /\ v a3 + v b3 < pow2 64 /\ v a4 + v b4 < pow2 64))
let lemma_fsum_0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  pow2_double_sum 51;
  pow2_lt_compat 64 52

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val factorization_lemma: unit ->
  Lemma (requires (True))
	(ensures  (forall a b c. {:pattern (a * (b+c))} a * (b + c) = a * b + a * c))
let factorization_lemma () = ()

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_fsum: h0:mem -> h1:mem -> a:bigint -> b:bigint -> Lemma
  (requires (norm h0 a /\ norm h0 b /\ isSum h0 h1 a b))
  (ensures  (norm h0 a /\ norm h0 b /\ isSum h0 h1 a b
    /\ bound52 h1 a /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length))
let lemma_fsum h0 h1 a b =
  pow2_double_sum 51;
  lemma_eval_bigint_5 h0 a;
  lemma_eval_bigint_5 h0 b;
  factorization_lemma ();
  lemma_eval_bigint_5 h1 a
