module Hacl.EC.Curve25519.Bignum.Modulo.Lemmas3

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
open Hacl.SBuffer
open FStar.Math.Lib
open FStar.Math.Lemmas
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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


let prime = pow2 255 - 19
(* let satisfiesModuloConstraints h b = satisfiesModuloConstraints h b *)
(* let isSum h h1 a b = isSum h h1 a b *)
(* let bound27 h b = bound27 h b *)
(* let w : U32.t -> Tot int = U32.v *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

let u51 = x:H64.t{v x < pow2 51}


let maskPrime mask b0 b1 b2 b3 b4 : Type0 =
  (v mask = pow2 64 - 1 ==> (v b4 = pow2 51 - 1 /\ v b3 = pow2 51 - 1 /\ v b2 = pow2 51 - 1 /\ v b1 = pow2 51 - 1 /\ v b0 >= pow2 51 - 19))
  /\ (v mask = 0 ==> (v b4 < pow2 51 - 1 \/ v b3 < pow2 51 -1 \/ v b2 < pow2 51 - 1 \/ v b1 < pow2 51 - 1 \/ v b0 < pow2 51 - 19))


let masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' : Type0 =
  (v mask = pow2 64 - 1 ==> (v b4' = v b4 - (pow2 51 - 1) /\ v b3' = v b3 - (pow2 51 - 1) /\ v b2' = v b2 - (pow2 51 - 1) /\ v b1' = v b1 - (pow2 51 - 1) /\ v b0' = v b0 - (pow2 51 - 19)))
  /\ (v mask = 0 ==> (v b4' = v b4 /\ v b3' = v b3 /\ v b2' = v b2 /\ v b1' = v b1 /\ v b0' = v b0))

let lemma_mult_le_left (a:pos) (b:nat) (c:nat) : Lemma (requires (b <= c)) (ensures (a * b <= a * c))
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_finalize_1:
  b0:u51 -> b1:u51 -> b2:u51 -> b3:u51 -> b4:u51 ->
  b0':u51 -> b1':u51 -> b2':u51 -> b3':u51 -> b4':u51 ->
  mask:H64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4' < pow2 255 - 19) )
let lemma_finalize_1 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  let res = v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4' in
  if v mask = pow2 64 - 1 then (
    cut (res < 19); assert_norm (19 < pow2 255 - 19)
  ) else (
    if (v b0 < pow2 51 - 19) then (
      lemma_mult_le_left (pow2 51) (v b1') (pow2 51 - 1);
      lemma_mult_le_left (pow2 102) (v b2') (pow2 51 - 1);
      lemma_mult_le_left (pow2 153) (v b3') (pow2 51 - 1);
      lemma_mult_le_left (pow2 204) (v b4') (pow2 51 - 1);
      cut (res <= (pow2 51 - 20) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1));
      assert_norm((pow2 51 - 20) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1) < pow2 255 - 19)
    ) else if (v b1 < pow2 51 - 1) then (
      lemma_mult_le_left (pow2 51) (v b1') (pow2 51 - 2);
      lemma_mult_le_left (pow2 102) (v b2') (pow2 51 - 1);
      lemma_mult_le_left (pow2 153) (v b3') (pow2 51 - 1);
      lemma_mult_le_left (pow2 204) (v b4') (pow2 51 - 1);
      cut (res <= (pow2 51 - 1) + pow2 51 * (pow2 51 - 2) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1));
      assert_norm((pow2 51 - 1) + pow2 51 * (pow2 51 - 2) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1) < pow2 255 - 19)
    ) else if (v b2 < pow2 51 - 1) then (
      lemma_mult_le_left (pow2 51) (v b1') (pow2 51 - 1);
      lemma_mult_le_left (pow2 102) (v b2') (pow2 51 - 2);
      lemma_mult_le_left (pow2 153) (v b3') (pow2 51 - 1);
      lemma_mult_le_left (pow2 204) (v b4') (pow2 51 - 1);
      cut (res <= (pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 2)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1));
      assert_norm((pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 2)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1) < pow2 255 - 19)
    ) else if (v b3 < pow2 51 - 1) then (
      lemma_mult_le_left (pow2 51) (v b1') (pow2 51 - 1);
      lemma_mult_le_left (pow2 102) (v b2') (pow2 51 - 1);
      lemma_mult_le_left (pow2 153) (v b3') (pow2 51 - 2);
      lemma_mult_le_left (pow2 204) (v b4') (pow2 51 - 1);
      cut (res <= (pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 2) + pow2 204 * (pow2 51 - 1));
      assert_norm((pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 2) + pow2 204 * (pow2 51 - 1) < pow2 255 - 19)
    ) else  (
      lemma_mult_le_left (pow2 51) (v b1') (pow2 51 - 1);
      lemma_mult_le_left (pow2 102) (v b2') (pow2 51 - 1);
      lemma_mult_le_left (pow2 153) (v b3') (pow2 51 - 1);
      lemma_mult_le_left (pow2 204) (v b4') (pow2 51 - 2);
      cut (res <= (pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 2));
      assert_norm((pow2 51 - 1) + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
          + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 2) < pow2 255 - 19)
    )
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val lemma_2_255m19_val: n:nat ->
  Lemma (requires (n = 255))
        (ensures  (pow2 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949))
        [SMTPat (pow2 n - 19)]
let lemma_2_255m19_val n = assert_norm (pow2 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949)


val lemma_finalize_2:
  b0:u51 -> b1:u51 -> b2:u51 -> b3:u51 -> b4:u51 ->
  b0':u51 -> b1':u51 -> b2':u51 -> b3':u51 -> b4':u51 ->
  mask:H64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  ((v b0 + pow2 51 * v b1 + pow2 102 * v b2 + pow2 153 * v b3 + pow2 204 * v b4) % (pow2 255 - 19) = (v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4') % (pow2 255 - 19)))
let lemma_finalize_2 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  let res = v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4' in
  let res0 = v b0 + pow2 51 * v b1 + pow2 102 * v b2 + pow2 153 * v b3 + pow2 204 * v b4 in
  if v mask = 0 then (
    ()
  ) else (
    cut (res = v b0 - (pow2 51 - 19) + pow2 51 * (v b1 - (pow2 51 - 1))
               + pow2 102 * (v b2 - (pow2 51 - 1)) + pow2 153 * (v b3 - (pow2 51 - 1))
               + 204 * (v b4 - (pow2 51 - 1)));
    distributivity_sub_right (pow2 51) (v b1) (pow2 51 - 1);
    distributivity_sub_right (pow2 102) (v b2) (pow2 51 - 1);
    distributivity_sub_right (pow2 153) (v b3) (pow2 51 - 1);
    distributivity_sub_right (pow2 204) (v b4) (pow2 51 - 1);
    cut (res = v b0 + pow2 51 * v b1 + pow2 102 * v b2 + pow2 153 * v b3 + pow2 204 * v b4
      - (pow2 51 - 19 + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
         + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1)));
    assert_norm ((pow2 51 - 19 + pow2 51 * (pow2 51 - 1) + pow2 102 * (pow2 51 - 1)
         + pow2 153 * (pow2 51 - 1) + pow2 204 * (pow2 51 - 1)) = pow2 255 - 19);
    cut (res0 = res + 1 * (pow2 255 - 19));
    Math.Lemmas.lemma_mod_plus res 1 (pow2 255 - 19)
  )


val lemma_finalize_3:
  b0:u51 -> b1:u51 -> b2:u51 -> b3:u51 -> b4:u51 ->
  b0':H64.t -> b1':H64.t -> b2':H64.t -> b3':H64.t -> b4':H64.t ->
  mask:H64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (v b0' < pow2 51 /\ v b1' < pow2 51 /\ v b2' < pow2 51 /\ v b3' < pow2 51 /\ v b4' < pow2 51))
let lemma_finalize_3 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  if v mask = 0 then ()
  else (assert_norm(pow2 51 > 19))


val lemma_finalize_0:
  b0:u51 -> b1:u51 -> b2:u51 -> b3:u51 -> b4:u51 ->
  b0':u51 -> b1':u51 -> b2':u51 -> b3':u51 -> b4':u51 ->
  mask:H64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  ((v b0 + pow2 51 * v b1 + pow2 102 * v b2 + pow2 153 * v b3 + pow2 204 * v b4) % (pow2 255 - 19) = (v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4')))
let lemma_finalize_0 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask =
  lemma_finalize_1 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  lemma_finalize_2 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  Math.Lemmas.modulo_lemma (v b0' + pow2 51 * v b1' + pow2 102 * v b2' + pow2 153 * v b3' + pow2 204 * v b4') (pow2 255 - 19)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_eval_5: h:HyperStack.mem -> b:bigint{live h b} -> Lemma
  (eval h b 5 = v (get h b 0) + pow2 51 * v (get h b 1) + pow2 102 * v (get h b 2) + pow2 153 * v (get h b 3) + pow2 204 * v (get h b 4))
let lemma_eval_5 h b =
  assert_norm(pow2 0 = 1);
  bitweight_def templ 4;
  bitweight_def templ 3;
  bitweight_def templ 2;
  bitweight_def templ 1;
  bitweight_def templ 0;
  eval_def h b 5;
  eval_def h b 4;
  eval_def h b 3;
  eval_def h b 2;
  eval_def h b 1;
  eval_def h b 0


val lemma_norm_5: h:HyperStack.mem -> b:bigint{live h b} -> Lemma
  (requires (v (get h b 0) < pow2 51 /\ v (get h b 1) < pow2 51 /\ v (get h b 2) < pow2 51 /\ v (get h b 3) < pow2 51 /\ v (get h b 4) < pow2 51))
  (ensures  (norm h b))
let lemma_norm_5 h b = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_finalize:
  h:HyperStack.mem ->
  b:bigint{norm h b} ->
  h':HyperStack.mem ->
  b':bigint{live h' b'} ->
  mask:H64.t{v mask = 0 \/ v mask = pow2 64 - 1} ->
  Lemma
    (requires (
      let b0 = (get h b 0) in let b1 = (get h b 1) in let b2 = (get h b 2) in
      let b3 = (get h b 3) in let b4 = (get h b 4) in
      let b0' = (get h' b' 0) in let b1' = (get h' b' 1) in let b2' = (get h' b' 2) in
      let b3' = (get h' b' 3) in let b4' = (get h' b' 4) in
      maskPrime mask b0 b1 b2 b3 b4 /\ masked mask b0 b1 b2 b3 b4 b0' b1' b2' b3' b4'))
    (ensures  (eval h' b' 5 = eval h b 5 % (pow2 255 - 19) /\ norm h' b'))
let lemma_finalize h b h' b' mask =
  let b0 = (get h b 0) in let b1 = (get h b 1) in let b2 = (get h b 2) in
  let b3 = (get h b 3) in let b4 = (get h b 4) in
  let b0' = (get h' b' 0) in let b1' = (get h' b' 1) in let b2' = (get h' b' 2) in
  let b3' = (get h' b' 3) in let b4' = (get h' b' 4) in
  lemma_eval_5 h b;
  lemma_eval_5 h' b';
  lemma_finalize_3 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask;
  lemma_finalize_0 b0 b1 b2 b3 b4 b0' b1' b2' b3' b4' mask
