module Hacl.Spec.Curve25519.Finv

open FStar.Mul
open Lib.IntTypes
open Spec.Curve25519

#reset-options "--z3rlimit 50 --max_fuel 2 --using_facts_from '* -FStar.Seq'"

let fsqr x = fmul x x

let one:elem =
  assert_norm (1 < prime);
  1

val pow: a:elem -> b:nat -> res:elem
let rec pow a b =
  if b = 0 then 1
  else fmul a (pow a (b - 1))

val lemma_pow_one: x:elem
  -> Lemma
    (requires True)
    (ensures  x == pow x 1)
let lemma_pow_one x =
  assert (pow x 1 == fmul x 1);
  FStar.Math.Lemmas.modulo_lemma x prime

val lemma_fmul_assoc: a:elem -> b:elem -> c:elem
  -> Lemma
    (fmul (fmul a b) c == fmul a (fmul b c))
let lemma_fmul_assoc a b c =
  let r = fmul (fmul a b) c in
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (a * b) c prime;
  FStar.Math.Lemmas.paren_mul_right a b c;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r a (b * c) prime

val lemma_pow_add: x:elem -> n:nat -> m:nat
  -> Lemma
    (requires True)
    (ensures  fmul (pow x n) (pow x m) == pow x (n + m))
let rec lemma_pow_add x n m =
  if n = 0 then FStar.Math.Lemmas.modulo_lemma (pow x m) prime
  else begin
    lemma_pow_add x (n - 1) m;
    lemma_fmul_assoc x (pow x (n - 1)) (pow x m)
  end

val lemma_pow_mul: x:elem -> n:nat -> m:nat
  -> Lemma
    (requires True)
    (ensures  pow (pow x n) m == pow x (n * m))
let rec lemma_pow_mul x n m =
  assert (n + n * (m - 1) = n * m);
  if m = 0 then ()
  else begin
    assert (pow (pow x n) m == fmul (pow x n) (pow (pow x n) (m - 1)));
    lemma_pow_mul x n (m - 1);
    assert (pow (pow x n) (m - 1) == pow x (n * (m - 1)));
    lemma_pow_add x n (n * (m - 1));
    assert (pow (pow x n) m == fmul (pow x n) (pow x (n * (m - 1))));
    assert (pow (pow x n) m == pow x (n + n * (m - 1)))
  end

val lemma_pow_double: a:elem -> b:nat ->
  Lemma
    (requires True)
    (ensures (pow (a *% a) b == pow a (b + b)))
  (decreases b)
let rec lemma_pow_double a b =
  if b = 0 then ()
  else begin
    lemma_pow_double a (b - 1);
    assert (pow (a *% a) b == fmul (a *% a) (pow (a *% a) (b - 1)));
    assert (pow (a *% a) b == fmul (a *% a) (pow a (b + b - 2)));
    lemma_pow_one a;
    lemma_pow_one a;
    //assert (pow (a *% a) b == fmul (fmul (pow a 1) (pow a 1)) (pow a (b + b - 2)));
    lemma_pow_add a 1 1;
    //assert (pow (a *% a) b == fmul (pow a 2) (pow a (b + b - 2)));
    lemma_pow_add a 2 (b + b - 2)
    //assert (pow (a *% a) b == pow a (b + b))
  end

val lemma_fpow_is_pow:a:elem -> b:pos ->
  Lemma
    (requires True)
    (ensures (fpow a b == pow a b))
  (decreases b)
let rec lemma_fpow_is_pow a b =
  if b = 1 then ()
  else begin
    if b % 2 = 0 then begin
      assert (fpow a b == fpow (a *% a) (b / 2));
      lemma_fpow_is_pow (a *% a) (b / 2);
      assert (fpow a b == pow (a *% a) (b / 2));
      lemma_pow_double a (b / 2) end
    else begin
      FStar.Math.Lemmas.euclidean_division_definition b 2;
      //assert (b == b / 2 * 2 + b % 2);
      assert (b > 1 /\ b % 2 = 1);
      assert (fpow a b == fmul a (fpow (a *% a) (b / 2)));
      lemma_fpow_is_pow (a *% a) (b / 2);
      //assert (fpow (a *% a) (b / 2) == pow (a *% a) (b / 2));
      assert (fpow a b == fmul a (pow (a *% a) (b / 2)));
      lemma_pow_double a (b / 2);
      //assert (fpow a b == fmul a (pow a (b / 2 * 2)));
      lemma_pow_one a;
      lemma_pow_add a 1 (b / 2 * 2) end
    end

val fsquare_times:
    inp:elem
  -> n:size_nat{0 < n}
  -> out:elem{out == pow inp (pow2 n)}
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
      lemma_pow_one out;
      lemma_pow_add out 1 1;
      lemma_pow_mul inp (pow2 (i + 1)) (pow2 1);
      assert_norm (pow2 (i + 1) * pow2 1 = pow2 (i + 2));
      assert (res == pow inp (pow2 (i + 2)));
      res) out in
  assert (out == pow inp (pow2 n));
  out

let pow_inv:nat =
  assert_norm (pow2 255 - 21 > 0);
  pow2 255 - 21

let pow_t0:nat =
  assert_norm (pow2 255 - pow2 5 > 0);
  pow2 255 - pow2 5

#set-options "--max_fuel 0 --max_ifuel 0"

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
  lemma_fpow_is_pow i (pow2 255 - 21);
  o
