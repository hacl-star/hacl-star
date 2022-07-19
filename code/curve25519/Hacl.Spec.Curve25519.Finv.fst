module Hacl.Spec.Curve25519.Finv

open FStar.Mul
open Spec.Curve25519
module M = Lib.NatMod
module LE = Lib.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let fsqr x = fmul x x
let pow = fpow
let cm_prime = M.mk_nat_mod_comm_monoid prime

val lemma_pow_mod_is_pow_cm : x:elem -> b:nat -> Lemma (pow x b = LE.pow cm_prime x b)
let lemma_pow_mod_is_pow_cm x b =
  M.lemma_pow_nat_mod_is_pow #prime x b;
  M.lemma_pow_mod #prime x b

val lemma_pow_one: x:elem -> Lemma (x == pow x 1)
let lemma_pow_one x =
  lemma_pow_mod_is_pow_cm x 1;
  LE.lemma_pow1 cm_prime x

val lemma_pow_add: x:elem -> n:nat -> m:nat ->
  Lemma (fmul (pow x n) (pow x m) == pow x (n + m))
let lemma_pow_add x n m =
  lemma_pow_mod_is_pow_cm x n;
  lemma_pow_mod_is_pow_cm x m;
  LE.lemma_pow_add cm_prime x n m;
  lemma_pow_mod_is_pow_cm x (n + m)

val lemma_pow_mul: x:elem -> n:nat -> m:nat ->
  Lemma (pow (pow x n) m == pow x (n * m))
let lemma_pow_mul x n m =
  lemma_pow_mod_is_pow_cm x n;
  lemma_pow_mod_is_pow_cm (pow x n) m;
  LE.lemma_pow_mul cm_prime x n m;
  lemma_pow_mod_is_pow_cm x (n * m)

val lemma_pow_double: a:elem -> b:nat ->
  Lemma (pow (a *% a) b == pow a (b + b))
let lemma_pow_double a b =
  lemma_pow_mod_is_pow_cm (a *% a) b;
  LE.lemma_pow_double cm_prime a b;
  lemma_pow_mod_is_pow_cm a (b + b)


val fsquare_times: inp:elem -> n:pos -> out:elem{out == pow inp (pow2 n)}
let fsquare_times inp n =
  let out = fsqr inp in
  lemma_pow_one inp;
  lemma_pow_add inp 1 1;
  assert_norm (pow2 1 = 2);
  assert (out == pow inp (pow2 1));
  let out =
    Lib.LoopCombinators.repeati_inductive #elem (n - 1)
    (fun i out -> out == pow inp (pow2 (i + 1)))
    (fun i out ->
      assert (out == pow inp (pow2 (i + 1)));
      let res = fsqr out in
      calc (==) {
        fmul out out;
        (==) { lemma_pow_add inp (pow2 (i + 1)) (pow2 (i + 1)) }
        pow inp (pow2 (i + 1) + pow2 (i + 1));
        (==) { Math.Lemmas.pow2_double_sum (i + 1) }
        pow inp (pow2 (i + 2));
      };
      res) out in
  assert (out == pow inp (pow2 n));
  out

let pow_t0:nat =
  assert_norm (pow2 255 - pow2 5 > 0);
  pow2 255 - pow2 5

val finv0: inp:elem ->
  Pure (tuple2 elem elem)
  (requires True)
  (ensures fun (a, t0) ->
    a == pow inp 11 /\
    t0 == pow inp pow_t0)
let finv0 i =
  (* 2 *)  let a  = fsquare_times i 1 in
  assert (a == pow i 2);
  (* 8 *)  let t0 = fsquare_times a 2 in
  assert (t0 == pow a 4);
  lemma_pow_mul i 2 4;
  assert (t0 == pow i 8);
  (* 9 *)  let b  = fmul t0 i in
  lemma_pow_one i;
  lemma_pow_add i 8 1;
  assert (b == pow i 9);
  (* 11 *) let a  = fmul b a in
  lemma_pow_add i 9 2;
  assert (a == pow i 11);
  (* 22 *) let t0 = fsquare_times a 1 in
  lemma_pow_mul i 11 2;
  assert (t0 == pow i 22);
  (* 2^5 - 2^0 = 31 *) let b = fmul t0 b in
  lemma_pow_add i 22 9;
  assert (b == pow i 31);
  (* 2^10 - 2^5 *) let t0 = fsquare_times b 5 in
  lemma_pow_mul i 31 (pow2 5);
  assert_norm (31 * pow2 5 = pow2 10 - pow2 5);
  assert (t0 == pow i (pow2 10 - pow2 5));
  (* 2^10 - 2^0 *) let b = fmul t0 b in
  assert_norm (31 = pow2 5 - 1);
  lemma_pow_add i (pow2 10 - pow2 5) (pow2 5 - 1);
  assert (b == pow i (pow2 10 - 1));
  (* 2^20 - 2^10 *) let t0 = fsquare_times b 10 in
  lemma_pow_mul i (pow2 10 - 1) (pow2 10);
  assert_norm ((pow2 10 - 1) * pow2 10 == pow2 20 - pow2 10);
  assert (t0 == pow i (pow2 20 - pow2 10));
  (* 2^20 - 2^0 *) let c = fmul t0 b in
  lemma_pow_add i (pow2 20 - pow2 10) (pow2 10 - 1);
  assert_norm (pow2 20 - pow2 10 + pow2 10 - 1 = pow2 20 - 1);
  assert (c == pow i (pow2 20 - 1));
  (* 2^40 - 2^20 *) let t0 = fsquare_times c 20 in
  lemma_pow_mul i (pow2 20 - 1) (pow2 20);
  assert_norm ((pow2 20 - 1) * pow2 20 = pow2 40 - pow2 20);
  assert (t0 == pow i (pow2 40 - pow2 20));
  (* 2^40 - 2^0 *) let t0 = fmul t0 c in
  lemma_pow_add i (pow2 40 -pow2 20) (pow2 20 - 1);
  assert_norm (pow2 40 - pow2 20 + pow2 20 - 1 = pow2 40 - 1);
  assert (t0 == pow i (pow2 40 - 1));
  (* 2^50 - 2^10 *) let t0 = fsquare_times t0 10 in
  lemma_pow_mul i (pow2 40 - 1) (pow2 10);
  assert_norm ((pow2 40 - 1) * pow2 10 = pow2 50 - pow2 10);
  assert (t0 == pow i (pow2 50 - pow2 10));
  (* 2^50 - 2^0 *) let b = fmul t0 b in
  lemma_pow_add i (pow2 50 - pow2 10) (pow2 10 - 1);
  assert_norm (pow2 50 - pow2 10 + pow2 10 - 1 = pow2 50 - 1);
  assert (b == pow i (pow2 50 - 1));
  (* 2^100 - 2^50 *) let t0 = fsquare_times b 50 in
  lemma_pow_mul i (pow2 50 - 1) (pow2 50);
  assert_norm ((pow2 50 - 1) * pow2 50 = pow2 100 - pow2 50);
  assert (t0 == pow i (pow2 100 - pow2 50));
  (* 2^100 - 2^0 *) let c = fmul t0 b in
  lemma_pow_add i (pow2 100 - pow2 50) (pow2 50 - 1);
  assert_norm (pow2 100 - pow2 50 + pow2 50 - 1 = pow2 100 - 1);
  assert (c == pow i (pow2 100 - 1));
  (* 2^200 - 2^100 *) let t0 = fsquare_times c 100 in
  lemma_pow_mul i (pow2 100 - 1) (pow2 100);
  assert_norm ((pow2 100 - 1) * pow2 100 = pow2 200 - pow2 100);
  assert (t0 == pow i (pow2 200 - pow2 100));
  (* 2^200 - 2^0 *) let t0 = fmul t0 c in
  lemma_pow_add i (pow2 200 - pow2 100) (pow2 100 - 1);
  assert_norm (pow2 200 - pow2 100 + pow2 100 - 1 = pow2 200 - 1);
  assert (t0 == pow i (pow2 200 - 1));
  (* 2^250 - 2^50 *) let t0 = fsquare_times t0 50 in
  lemma_pow_mul i (pow2 200 - 1) (pow2 50);
  assert_norm ((pow2 200 - 1) * pow2 50 = pow2 250 - pow2 50);
  assert (t0 == pow i (pow2 250 - pow2 50));
  (* 2^250 - 2^0 *) let t0 = fmul t0 b in
  lemma_pow_add i (pow2 250 - pow2 50) (pow2 50 - 1);
  assert_norm (pow2 250 - pow2 50 + pow2 50 - 1 = pow2 250 - 1);
  assert (t0 == pow i (pow2 250 - 1));
  (* 2^255 - 2^5 *) let t0 = fsquare_times t0 5 in
  lemma_pow_mul i (pow2 250 - 1) (pow2 5);
  assert_norm ((pow2 250 - 1) * pow2 5 = pow2 255 - pow2 5);
  assert (t0 == pow i (pow2 255 - pow2 5));
  a, t0

val finv: inp:elem -> out:elem{out == fpow inp (pow2 255 - 21)}
let finv i =
  let a, t0 = finv0 i in
  (* 2^255 - 21 *) let o = fmul t0 a in
  lemma_pow_add i (pow2 255 - pow2 5) 11;
  assert_norm (pow2 255 - pow2 5 + 11 = pow2 255 - 21);
  assert (o == pow i (pow2 255 - 21));
  o
