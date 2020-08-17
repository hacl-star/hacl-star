module Hacl.Spec.Karatsuba.Lemmas

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

type sign =
  | Positive
  | Negative

let abs (a:nat) (b:nat) : nat =
  if a < b then b - a else a - b

val sign_abs: a:nat -> b:nat ->
  Pure (tuple2 sign nat)
  (requires True)
  (ensures  fun (s, res) -> res == abs a b /\
    s == (if a < b then Negative else Positive))

let sign_abs a b =
  if a < b then (Negative, b - a) else (Positive, a - b)


val lemma_double_p: i:pos -> aLen:nat{aLen == pow2 i} -> Lemma
  (let p = pow2 (aLen / 2 * 64) in p * p == pow2 (64 * aLen))
let lemma_double_p i aLen =
  let p = pow2 (aLen / 2 * 64) in
  calc (==) {
    p * p;
    (==) { Math.Lemmas.pow2_plus (aLen / 2 * 64) (aLen / 2 * 64) }
    pow2 (aLen / 2 * 64 + aLen / 2 * 64);
    (==) { Math.Lemmas.distributivity_add_left (aLen / 2) (aLen / 2) 64 }
    pow2 ((aLen / 2 * 2) * 64);
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 1 i; Math.Lemmas.lemma_div_exact aLen 2 }
    pow2 (aLen * 64);
    }


val lemma_bn_halves: i:pos -> aLen:nat{aLen == pow2 i} -> a:nat{a < pow2 (64 * aLen)} ->
  Lemma (let p = pow2 (aLen / 2 * 64) in a / p < p /\ a % p < p /\ a == a / p * p + a % p)
let lemma_bn_halves i aLen a = lemma_double_p i aLen


val lemma_middle_karatsuba: a0:nat -> a1:nat -> b0:nat -> b1:nat ->
  Lemma
   (let s0, t0 = sign_abs a0 a1 in
    let s1, t1 = sign_abs b0 b1 in
    let t23 = t0 * t1 in
    let t01 = a0 * b0 + a1 * b1 in
    let t45 = if s0 = s1 then t01 - t23 else t01 + t23 in
    t45 == a0 * b1 + a1 * b0)

let lemma_middle_karatsuba a0 a1 b0 b1 = ()


val lemma_karatsuba: i:pos -> aLen:nat{aLen == pow2 i} -> a0:nat -> a1:nat -> b0:nat -> b1:nat -> Lemma
  (let aLen2 = aLen / 2 in
   let p = pow2 (64 * aLen2) in
   let a = a1 * p + a0 in
   let b = b1 * p + b0 in
   a1 * b1 * pow2 (64 * aLen) + (a0 * b1 + a1 * b0) * pow2 (64 * aLen2) + a0 * b0 == a * b)

let lemma_karatsuba i aLen a0 a1 b0 b1 =
  let aLen2 = aLen / 2 in
  let p = pow2 (64 * aLen2) in
  let a = a1 * p + a0 in
  let b = b1 * p + b0 in

  calc (==) {
    a * b;
    (==) { }
    (a1 * p + a0) * (b1 * p + b0);
    (==) { }
    a1 * p * (b1 * p + b0) + a0 * (b1 * p + b0);
    (==) { }
    a1 * p * (b1 * p) + a1 * p * b0 + a0 * (b1 * p) + a0 * b0;
    (==) { Math.Lemmas.paren_mul_right a0 b1 p }
    a1 * p * (b1 * p) + a1 * p * b0 + a0 * b1 * p + a0 * b0;
    (==) { Math.Lemmas.paren_mul_right a1 p (b1 * p); Math.Lemmas.paren_mul_right p p b1 }
    a1 * (b1 * (p * p)) + a1 * p * b0 + a0 * b1 * p + a0 * b0;
    (==) { Math.Lemmas.paren_mul_right a1 b1 (p * p) }
    a1 * b1 * (p * p) + a1 * p * b0 + a0 * b1 * p + a0 * b0;
    (==) { lemma_double_p i aLen }
    a1 * b1 * pow2 (64 * aLen) + a1 * p * b0 + a0 * b1 * p + a0 * b0;
    (==) { Math.Lemmas.paren_mul_right a1 p b0; Math.Lemmas.paren_mul_right a1 b0 p }
    a1 * b1 * pow2 (64 * aLen) + a1 * b0 * p + a0 * b1 * p + a0 * b0;
    (==) { Math.Lemmas.distributivity_add_left (a1 * b0) (a0 * b1) p }
    a1 * b1 * pow2 (64 * aLen) + (a1 * b0 + a0 * b1) * p + a0 * b0;
   }


val karatsuba:
    i:nat -> aLen:nat{aLen == pow2 i}
  -> a:nat{a < pow2 (64 * aLen)}
  -> b:nat{b < pow2 (64 * aLen)} ->
  Tot (res:nat{res == a * b}) (decreases aLen)

let rec karatsuba i aLen a b =
  if aLen < 16 then a * b
  else begin
    let aLen2 = aLen / 2 in
    let i2 = i - 1 in
    Math.Lemmas.pow2_double_mult (i - 1);
    assert (aLen2 == pow2 (i - 1));
    let p = pow2 (64 * aLen2) in
    Math.Lemmas.pow2_minus (64 * aLen) (64 * aLen2);

    let a0 = a % p in let a1 = a / p in
    let b0 = b % p in let b1 = b / p in
    lemma_bn_halves i aLen a;
    lemma_bn_halves i aLen b;

    let s0, t0 = sign_abs a0 a1 in
    let s1, t1 = sign_abs b0 b1 in

    let t23 = karatsuba i2 aLen2 t0 t1 in assert (t23 == t0 * t1);
    let r01 = karatsuba i2 aLen2 a0 b0 in assert (r01 == a0 * b0);
    let r23 = karatsuba i2 aLen2 a1 b1 in assert (r23 == a1 * b1);

    let t01 = r01 + r23 in assert (t01 == a0 * b0 + a1 * b1);
    let t45 = if s0 = s1 then t01 - t23 else t01 + t23 in
    lemma_middle_karatsuba a0 a1 b0 b1;
    assert (t45 == a0 * b1 + a1 * b0);

    let res = r23 * pow2 (64 * aLen) + t45 * p + r01 in
    lemma_karatsuba i aLen a0 a1 b0 b1;
    res end
