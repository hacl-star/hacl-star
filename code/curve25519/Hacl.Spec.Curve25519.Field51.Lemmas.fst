module Hacl.Spec.Curve25519.Field51.Lemmas

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes

open FStar.Tactics
open FStar.Tactics.Canon

open Spec.Curve25519
open Hacl.Spec.Curve25519.Field51.Definition

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --using_facts_from '* -FStar.Seq -FStar.Tactics'"

val lemma_mod_sub_distr: a:int -> b:int -> n:pos ->
  Lemma ((a - b % n) % n = (a - b) % n)
let lemma_mod_sub_distr a b n =
  FStar.Math.Lemmas.lemma_div_mod b n;
  FStar.Math.Lemmas.distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  FStar.Math.Lemmas.lemma_mod_plus (a - (b % n)) (-(b / n)) n

val lemma_mul5_distr_r:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma ((a + b + c + d + e) * f == a * f + b * f + c * f + d * f + e * f)
let lemma_mul5_distr_r a b c d e f = ()

val lemma_mul5_distr_l:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_mul_assos_3:
  a:nat -> b:nat -> c:nat ->
  Lemma (a * b * c == a * (b * c))
let lemma_mul_assos_3 a b c = ()

val lemma_mul_assos_4:
  a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma (a * b * c * d == a * (b * c * d))
let lemma_mul_assos_4 a b c d = ()

val lemma_mul_assos_5:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat ->
  Lemma (a * b * c * d * e == a * (b * c * d * e))
let lemma_mul_assos_5 a b c d e = ()

val lemma_mul_assos_6:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * b * c * d * e * f == a * (b * c * d * e * f))
let lemma_mul_assos_6 a b c d e f = ()

val lemma_add_le:a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma
  (requires a <= b /\ c <= d)
  (ensures  a + c <= b + d)
let lemma_add_le a b c d = ()

val lemma_mul_le:a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma
  (requires a <= b /\ c <= d)
  (ensures  a * c <= b * d)
let lemma_mul_le a b c d = ()

val lemma_prime: unit ->
  Lemma (pow2 255 % prime = 19)
let lemma_prime () =
  assert_norm (pow2 255 % prime = 19 % prime);
  assert_norm (19 < prime);
  FStar.Math.Lemmas.modulo_lemma 19 prime

val lemma_add_zero:
  f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> Lemma (
    let (f10, f11, f12, f13, f14) = f1 in
    let o0 = f10 +! u64 0x3fffffffffff68 in
    let o1 = f11 +! u64 0x3ffffffffffff8 in
    let o2 = f12 +! u64 0x3ffffffffffff8 in
    let o3 = f13 +! u64 0x3ffffffffffff8 in
    let o4 = f14 +! u64 0x3ffffffffffff8 in
    let out = (o0, o1, o2, o3, o4) in
    feval out == feval f1)
let lemma_add_zero f1 =
  let (f10, f11, f12, f13, f14) = f1 in
  let o0 = f10 +! u64 0x3fffffffffff68 in
  let o1 = f11 +! u64 0x3ffffffffffff8 in
  let o2 = f12 +! u64 0x3ffffffffffff8 in
  let o3 = f13 +! u64 0x3ffffffffffff8 in
  let o4 = f14 +! u64 0x3ffffffffffff8 in
  let out = (o0, o1, o2, o3, o4) in
  assert (feval out ==
    (v f10 + 0x3fffffffffff68 +
    (v f11 + 0x3ffffffffffff8) * pow51 +
    (v f12 + 0x3ffffffffffff8) * pow51 * pow51 +
    (v f13 + 0x3ffffffffffff8) * pow51 * pow51 * pow51 +
    (v f14 + 0x3ffffffffffff8) * pow51 * pow51 * pow51 * pow51) % prime);
  FStar.Math.Lemmas.distributivity_add_left (v f11) 0x3ffffffffffff8 pow51;
  FStar.Math.Lemmas.distributivity_add_left (v f12) 0x3ffffffffffff8 (pow51 * pow51);
  FStar.Math.Lemmas.distributivity_add_left (v f13) 0x3ffffffffffff8 (pow51 * pow51 * pow51);
  FStar.Math.Lemmas.distributivity_add_left (v f14) 0x3ffffffffffff8 (pow51 * pow51 * pow51 * pow51);
  assert_norm (
    0x3fffffffffff68 +
    0x3ffffffffffff8 * pow51 +
    0x3ffffffffffff8 * pow51 * pow51 +
    0x3ffffffffffff8 * pow51 * pow51 * pow51 +
    0x3ffffffffffff8 * pow51 * pow51 * pow51 * pow51 = 8 * prime);
  assert (feval out == (v f10 + v f11 * pow51 +
    v f12 * pow51 * pow51 + v f13 * pow51 * pow51 * pow51 +
    v f14 * pow51 * pow51 * pow51 * pow51 + 8 * prime) % prime);
  FStar.Math.Lemmas.lemma_mod_plus (as_nat5 f1) 8 prime;
  assert (feval out == (v f10 + v f11 * pow51 +
    v f12 * pow51 * pow51 + v f13 * pow51 * pow51 * pow51 +
    v f14 * pow51 * pow51 * pow51 * pow51) % prime)

val lemma_fmul5_pow51: r:felem5
  -> Lemma
    (requires (let (r0, r1, r2, r3, r4) = r in
      v r4 * 19 <= 190 * pow51))
    (ensures (let (r0, r1, r2, r3, r4) = r in
      (pow51 * as_nat5 r) % prime == as_nat5 (r4 *! u64 19, r0, r1, r2, r3) % prime))
let lemma_fmul5_pow51 r =
  let (r0, r1, r2, r3, r4) = r in
  assert (pow51 * as_nat5 r == pow51 * (v r0 + v r1 * pow51 + v r2 * pow51 * pow51 +
    v r3 * pow51 * pow51 * pow51 + v r4 * pow51 * pow51 * pow51 * pow51));
  lemma_mul5_distr_l pow51 (v r0) (v r1 * pow51) (v r2 * pow51 * pow51)
    (v r3 * pow51 * pow51 * pow51) (v r4 * pow51 * pow51 * pow51 * pow51);

  let p51r0123 = pow51 * v r0 + pow51 * v r1 * pow51 +
    pow51 * v r2 * pow51 * pow51 + pow51 * v r3 * pow51 * pow51 * pow51 in
  let p51r4 = pow51 * v r4 * pow51 * pow51 * pow51 * pow51 in
  assert ((pow51 * as_nat5 r) % prime == (p51r0123 + p51r4) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_r p51r0123 p51r4 prime;
  assert_norm (p51r4 % prime == (v r4 * pow2 255) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v r4) (pow2 255) prime;
  lemma_prime ();
  assert_norm ((v r4 * pow2 255) % prime == (v r4 * 19) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r p51r0123 (v r4 * 19) prime

val lemma_fmul5_pow51_pow51:r:felem5
  -> Lemma
    (requires (let (r0, r1, r2, r3, r4) = r in
      v r4 * 19 <= 190 * pow51 /\ v r3 * 19 <= 190 * pow51))
    (ensures (let (r0, r1, r2, r3, r4) = r in
      (pow51 * pow51 * as_nat5 r) % prime ==
       as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) % prime))
let lemma_fmul5_pow51_pow51 r =
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_3 pow51 pow51 (as_nat5 r);
  let p51r = pow51 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 p51r prime;
  assert ((pow51 * pow51 * as_nat5 r) % prime == (pow51 * (p51r % prime)) % prime);
  lemma_fmul5_pow51 r;
  assert ((pow51 * pow51 * as_nat5 r) % prime ==
    (pow51 * (as_nat5 (r4 *! u64 19, r0, r1, r2, r3) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r4 *! u64 19, r0, r1, r2, r3)) prime;
  lemma_fmul5_pow51 (r4 *! u64 19, r0, r1, r2, r3);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2)) prime

val lemma_fmul5_pow51_pow51_pow51: r:felem5
  -> Lemma
    (requires (let (r0, r1, r2, r3, r4) = r in
      v r4 * 19 <= 190 * pow51 /\ v r3 * 19 <= 190 * pow51 /\
      v r2 * 19 <= 190 * pow51))
    (ensures (let (r0, r1, r2, r3, r4) = r in
      (pow51 * pow51 * pow51 * as_nat5 r) % prime ==
       as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) % prime))
let lemma_fmul5_pow51_pow51_pow51 r =
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_4 pow51 pow51 pow51 (as_nat5 r);
  let p51p51r = pow51 * pow51 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 p51p51r prime;
  assert ((pow51 * pow51 * pow51 * as_nat5 r) % prime == (pow51 * (p51p51r % prime)) % prime);
  lemma_fmul5_pow51_pow51 r;
  assert ((pow51 * pow51 * pow51 * as_nat5 r) % prime ==
    (pow51 * (as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2)) prime;
  lemma_fmul5_pow51 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1)) prime

val lemma_fmul5_pow51_pow51_pow51_pow51: r:felem5
  -> Lemma
    (requires (let (r0, r1, r2, r3, r4) = r in
      v r4 * 19 <= 190 * pow51 /\ v r3 * 19 <= 190 * pow51 /\
      v r2 * 19 <= 190 * pow51 /\ v r1 * 19 <= 190 * pow51))
    (ensures (let (r0, r1, r2, r3, r4) = r in
      (pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime ==
       as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0) % prime))
let lemma_fmul5_pow51_pow51_pow51_pow51 r =
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_5 pow51 pow51 pow51 pow51 (as_nat5 r);
  let p51p51p51r = pow51 * pow51 * pow51 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 p51p51p51r prime;
  assert ((pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime == (pow51 * (p51p51p51r % prime)) % prime);
  lemma_fmul5_pow51_pow51_pow51 r;
  assert ((pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime ==
    (pow51 * (as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1)) prime;
  lemma_fmul5_pow51 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow51 (as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0)) prime

val lemma_fmul5_1:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> Lemma
    (requires (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * pow51 * as_nat5 r +
      v f12 * pow51 * pow51 * as_nat5 r +
      v f13 * pow51 * pow51 * pow51 * as_nat5 r +
      v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * pow51 * pow51 * as_nat5 r +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
let lemma_fmul5_1 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  assert (v r4 * 19 <= 190 * max51);
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * pow51 * as_nat5 r +
     v f12 * pow51 * pow51 * as_nat5 r +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f11 * pow51 * as_nat5 r)
    (v f10 * as_nat5 r +
     v f12 * pow51 * pow51 * as_nat5 r +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime;
  lemma_mul_assos_3 (v f11) pow51 (as_nat5 r);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (pow51 * as_nat5 r) prime;
  lemma_fmul5_pow51 (r0, r1, r2, r3, r4);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (as_nat5 (r4 *! u64 19, r0, r1, r2, r3)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3))
    (v f10 * as_nat5 r +
     v f12 * pow51 * pow51 * as_nat5 r +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime

val lemma_fmul5_2:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> Lemma
    (requires (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
      v f12 * pow51 * pow51 * as_nat5 r +
      v f13 * pow51 * pow51 * pow51 * as_nat5 r +
      v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
let lemma_fmul5_2 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_4 (v f12) pow51 pow51 (as_nat5 r);
  let p51p51r = pow51 * pow51 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * p51p51r +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f12 * p51p51r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) p51p51r prime;
  lemma_fmul5_pow51_pow51 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) (as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f13 * pow51 * pow51 * pow51 * as_nat5 r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime

val lemma_fmul5_3:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> Lemma
    (requires (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
      v f13 * pow51 * pow51 * pow51 * as_nat5 r +
      v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
let lemma_fmul5_3 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_5 (v f13) pow51 pow51 pow51 (as_nat5 r);
  let p51p51p51r = pow51 * pow51 * pow51 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * p51p51p51r +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f13 * p51p51p51r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) p51p51p51r prime;
  lemma_fmul5_pow51_pow51_pow51 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) (as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) prime

val lemma_fmul5_4:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> Lemma
    (requires (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
      v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) +
      v f14 * pow51 * pow51 * pow51 * pow51 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) +
     v f14 * as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0)) % prime))
let lemma_fmul5_4 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_6 (v f14) pow51 pow51 pow51 pow51 (as_nat5 r);
  let p51p51p51p51r = pow51 * pow51 * pow51 * pow51 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) +
     v f14 * p51p51p51p51r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f14 * p51p51p51p51r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1)) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) p51p51p51p51r prime;
  lemma_fmul5_pow51_pow51_pow51_pow51 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) (as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f14 * as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1)) prime

val lemma_fmul5:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> Lemma
   (let (f10, f11, f12, f13, f14) = f1 in
    let (r0, r1, r2, r3, r4) = r in
    fmul (feval f1) (feval r) ==
     (v f10 * as_nat5 (r0, r1, r2, r3, r4) +
      v f11 * as_nat5 (r4 *! u64 19, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 19, r4 *! u64 19, r0, r1, r2) +
      v f13 * as_nat5 (r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0, r1) +
      v f14 * as_nat5 (r1 *! u64 19, r2 *! u64 19, r3 *! u64 19, r4 *! u64 19, r0)) % prime)
let lemma_fmul5 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 + v f11 * pow51 + v f12 * pow51 * pow51 + v f13 * pow51 * pow51 * pow51 +
    v f14 * pow51 * pow51 * pow51 * pow51) * as_nat5 r % prime);
  lemma_mul5_distr_r (v f10) (v f11 * pow51) (v f12 * pow51 * pow51)
    (v f13 * pow51 * pow51 * pow51) (v f14 * pow51 * pow51 * pow51 * pow51) (as_nat5 r);
  lemma_fmul5_1 f1 r;
  lemma_fmul5_2 f1 r;
  lemma_fmul5_3 f1 r;
  lemma_fmul5_4 f1 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 f1) (as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat5 f1 % prime) (as_nat5 r) prime

val lemma_smul_felem5:
    u1:uint64
  -> f2:felem5
  -> Lemma (
      let (f20, f21, f22, f23, f24) = f2 in
      v u1 * as_nat5 f2 == v u1 * v f20 + v u1 * v f21 * pow51 +
      v u1 * v f22 * pow51 * pow51 + v u1 * v f23 * pow51 * pow51 * pow51 +
      v u1 * v f24 * pow51 * pow51 * pow51 * pow51)
let lemma_smul_felem5 u1 f2 = ()
  // let (f20, f21, f22, f23, f24) = f2 in
  // assert (as_nat5 f2 == v f20 + v f21 * pow51 + v f22 * pow51 * pow51 +
  //   v f23 * pow51 * pow51 * pow51 + v f24 * pow51 * pow51 * pow51 * pow51);
  // lemma_mul5_distr_l (v u1) (v f20) (v f21 * pow51) (v f22 * pow51 * pow51)
  //   (v f23 * pow51 * pow51 * pow51) (v f24 * pow51 * pow51 * pow51 * pow51)

val lemma_smul_add_felem5:
    u1:uint64
  -> f2:felem5
  -> acc1:felem_wide5
  -> Lemma (let (f20, f21, f22, f23, f24) = f2 in
      let (o0, o1, o2, o3, o4) = acc1 in
      wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 ==
      v o0 + v o1 * pow51 + v o2 * pow51 * pow51 +
      v o3 * pow51 * pow51 * pow51 + v o4 * pow51 * pow51 * pow51 * pow51 +
      v u1 * v f20 + v u1 * v f21 * pow51 +
      v u1 * v f22 * pow51 * pow51 + v u1 * v f23 * pow51 * pow51 * pow51 +
      v u1 * v f24 * pow51 * pow51 * pow51 * pow51)
let lemma_smul_add_felem5 u1 f2 acc1 = ()
  // let (f20, f21, f22, f23, f24) = f2 in
  // let (o0, o1, o2, o3, o4) = acc1 in
  // lemma_mul5_distr_l (v u1) (v f20) (v f21 * pow51) (v f22 * pow51 * pow51)
  //   (v f23 * pow51 * pow51 * pow51) (v f24 * pow51 * pow51 * pow51 * pow51)

val lemma_carry51:
    l:uint64
  -> cin:uint64
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 8190)
    (ensures (let l0 = (l +! cin) &. mask51 in
      let l1 = (l +! cin) >>. 51ul in
      v l + v cin == v l1 * pow2 51 + v l0 /\
      felem_fits1 l0 1 /\ v l1 < pow2 13))
let lemma_carry51 l cin =
  let l' = l +! cin in
  let l0 = l' &. mask51 in
  let l1 = l' >>. 51ul in
  mod_mask_lemma (to_u64 l') 51ul;
  uintv_extensionality (mod_mask #U64 #SEC 51ul) mask51;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 51 64;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 51);
  FStar.Math.Lemmas.pow2_minus 64 51

val lemma_carry51_wide:
    #m:scale64{m < 8192}
  -> l:uint128{felem_wide_fits1 l m}
  -> cin:uint64
  -> Lemma (
      let l' = l +! to_u128 cin in
      let l0 = (to_u64 l') &. mask51 in
      let l1 = to_u64 (l' >>. 51ul) in
      v l + v cin == v l1 * pow2 51 + v l0 /\
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1))
let lemma_carry51_wide #m l cin =
  let l' = l +! to_u128 cin in
  //assert_norm (8192 * pow51 * pow51 == pow2 115);
  //assert (v l' < pow2 115);
  let l0 = (to_u64 l') &. mask51 in
  let l1 = to_u64 (l' >>. 51ul) in
  mod_mask_lemma (to_u64 l') 51ul;
  uintv_extensionality (mod_mask #U64 #SEC 51ul) mask51;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 51 64;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 51)

val lemma_carry5_simplify:
  c0:uint64 -> c1:uint64 -> c2:uint64 -> c3:uint64 -> c4:uint64 ->
  t0:uint64 -> t1:uint64 -> t2:uint64 -> t3:uint64 -> t4:uint64 ->
  Lemma
   ((v c0 * pow2 51 + v t0 +
    (v c1 * pow2 51 + v t1 - v c0) * pow51 +
    (v c2 * pow2 51 + v t2 - v c1) * pow51 * pow51 +
    (v c3 * pow2 51 + v t3 - v c2) * pow51 * pow51 * pow51 +
    (v c4 * pow2 51 + v t4 - v c3) * pow51 * pow51 * pow51 * pow51) % prime ==
    (v t0 + v c4 * 19 + v t1 * pow51 + v t2 * pow51 * pow51 +
     v t3 * pow51 * pow51 * pow51 + v t4 * pow51 * pow51 * pow51 * pow51) % prime)
let lemma_carry5_simplify c0 c1 c2 c3 c4 t0 t1 t2 t3 t4 =
  assert_norm (pow51 = pow2 51);
  assert (
    v c0 * pow2 51 + v t0 +
    (v c1 * pow2 51 + v t1 - v c0) * pow51 +
    (v c2 * pow2 51 + v t2 - v c1) * pow51 * pow51 +
    (v c3 * pow2 51 + v t3 - v c2) * pow51 * pow51 * pow51 +
    (v c4 * pow2 51 + v t4 - v c3) * pow51 * pow51 * pow51 * pow51 ==
    v t0 + v t1 * pow51 + v t2 * pow51 * pow51 + v t3 * pow51 * pow51 * pow51 +
    v t4 * pow51 * pow51 * pow51 * pow51 + v c4 * pow2 51 * pow51 * pow51 * pow51 * pow51);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow51 +
    v t2 * pow51 * pow51 +
    v t3 * pow51 * pow51 * pow51 +
    v t4 * pow51 * pow51 * pow51 * pow51)
   (v c4 * pow2 51 * pow51 * pow51 * pow51 * pow51) prime;
  lemma_mul_assos_6 (v c4) (pow2 51) pow51 pow51 pow51 pow51;
  assert_norm (pow2 51 * pow51 * pow51 * pow51 * pow51 = pow2 255);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c4) (pow2 255) prime;
  lemma_prime ();
  assert_norm ((v c4 * pow2 255) % prime == (v c4 * 19) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (v t0 + v t1 * pow51 +
    v t2 * pow51 * pow51 +
    v t3 * pow51 * pow51 * pow51 +
    v t4 * pow51 * pow51 * pow51 * pow51)
   (v c4 * 19) prime

val lemma_load_felem5:
    f:felem5
  -> u64s:LSeq.lseq uint64 4
  -> Lemma
    (requires (
      let open Lib.Sequence in
      let (f0, f1, f2, f3, f4) = f in
      let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in
      v f0 == v s0 % pow2 51 /\
      v f1 == v s0 / pow2 51 + (v s1 % pow2 38) * pow2 13 /\
      v f2 == v s1 / pow2 38 + (v s2 % pow2 25) * pow2 26 /\
      v f3 == v s2 / pow2 25 + (v s3 % pow2 12) * pow2 39 /\
      v f4 == v s3 / pow2 12))
    (ensures as_nat5 f == BSeq.nat_from_intseq_le u64s)
let lemma_load_felem5 f u64s =
  let open Lib.Sequence in
  let (f0, f1, f2, f3, f4) = f in
  let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in
  assert_norm (pow51 = pow2 51);
  FStar.Math.Lemmas.euclidean_division_definition (v s0) (pow2 51);
  assert_norm (pow2 13 * pow2 51 = pow2 64);
  assert_norm (pow2 51 * pow2 51 = pow2 38 * pow2 64);
  FStar.Math.Lemmas.euclidean_division_definition (v s1) (pow2 38);
  assert_norm (pow2 26 * pow2 51 * pow2 51 = pow2 128);
  assert_norm (pow2 51 * pow2 51 * pow2 51 = pow2 25 * pow2 128);
  FStar.Math.Lemmas.euclidean_division_definition (v s2) (pow2 25);
  assert_norm (pow2 39 * pow2 51 * pow2 51 * pow2 51 = pow2 192);
  assert_norm (pow2 51 * pow2 51 * pow2 51 * pow2 51 = pow2 12 * pow2 192);
  FStar.Math.Lemmas.euclidean_division_definition (v s3) (pow2 12);
  assert (as_nat5 f == v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192);
  Hacl.Impl.Curve25519.Lemmas.lemma_nat_from_uints64_le_4 u64s;
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192)

val lemma_load_felem_fits5:
    f:felem5
  -> u64s:LSeq.lseq uint64 4
  -> Lemma
    (requires (
      let open Lib.Sequence in
      let (f0, f1, f2, f3, f4) = f in
      let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in
      v s3 < pow2 63 /\
      v f0 == v s0 % pow2 51 /\
      v f1 == v s0 / pow2 51 + (v s1 % pow2 38) * pow2 13 /\
      v f2 == v s1 / pow2 38 + (v s2 % pow2 25) * pow2 26 /\
      v f3 == v s2 / pow2 25 + (v s3 % pow2 12) * pow2 39 /\
      v f4 == v s3 / pow2 12))
    (ensures felem_fits5 f (1, 1, 1, 1, 1))
let lemma_load_felem_fits5 f u64s =
  let open Lib.Sequence in
  let (f0, f1, f2, f3, f4) = f in
  let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in
  assert_norm (pow51 = pow2 51);
  assert (v f0 < pow2 51);
  FStar.Math.Lemmas.lemma_div_lt (v s3) 63 12;
  assert (v f4 < pow2 51);
  FStar.Math.Lemmas.lemma_div_lt (v s0) 64 51;
  lemma_mul_le (v s1 % pow2 38) (pow2 38 - 1) (pow2 13) (pow2 13);
  assert ((v s1 % pow2 38) * pow2 13 <= (pow2 38 - 1) * pow2 13);
  assert (v f1 <= pow2 13 - 1 + (pow2 38 - 1) * pow2 13);
  assert (v f1 <= pow2 38 * pow2 13 - 1);
  assert_norm (pow2 38 * pow2 13 = pow2 51);
  assert (v f1 < pow2 51);
  FStar.Math.Lemmas.lemma_div_lt (v s1) 64 38;
  lemma_mul_le (v s2 % pow2 25) (pow2 25 - 1) (pow2 26) (pow2 26);
  assert ((v s2 % pow2 25) * pow2 26 <= (pow2 25 - 1) * pow2 26);
  assert (v f2 <= (pow2 26 - 1) + (pow2 25 - 1) * pow2 26);
  assert (v f2 <= pow2 25 * pow2 26 - 1);
  assert_norm (pow2 25 * pow2 26 = pow2 51);
  assert (v f2 < pow2 51);
  FStar.Math.Lemmas.lemma_div_lt (v s2) 64 25;
  lemma_mul_le (v s3 % pow2 12) (pow2 12 - 1) (pow2 39) (pow2 39);
  assert ((v s3 % pow2 12) * pow2 39 <= (pow2 12 - 1) * pow2 39);
  assert (v f3 <= (pow2 39 - 1) + (pow2 12 - 1) * pow2 39);
  assert (v f3 <= pow2 12 * pow2 39 - 1);
  assert_norm (pow2 12 * pow2 39 = pow2 51);
  assert (v f3 < pow2 51)

val lemma_load_felem: u64s:LSeq.lseq uint64 4{v (u64s.[3]) < pow2 63} ->
  Lemma (
    let open Lib.Sequence in
    let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in
    let f0 = s0 &. mask51 in
    let f1 = (s0 >>. 51ul) |. ((s1 &. u64 0x3fffffffff) <<. 13ul) in
    let f2 = (s1 >>. 38ul) |. ((s2 &. u64 0x1ffffff) <<. 26ul) in
    let f3 = (s2 >>. 25ul) |. ((s3 &. u64 0xfff) <<. 39ul) in
    let f4 = s3 >>. 12ul in
    let f = (f0, f1, f2, f3, f4) in
    felem_fits5 f (1, 1, 1, 1, 1) /\
    as_nat5 f == BSeq.nat_from_intseq_le u64s)
let lemma_load_felem u64s =
  assert_norm (0x3fffffffff = pow2 38 - 1);
  assert_norm (0x1ffffff = pow2 25 - 1);
  assert_norm (0xfff = pow2 12 - 1);
  let open Lib.Sequence in
  let (s0, s1, s2, s3) = (u64s.[0], u64s.[1], u64s.[2], u64s.[3]) in

  let f0l = s0 &. mask51 in
  mod_mask_lemma s0 51ul;
  uintv_extensionality (mod_mask #U64 51ul) mask51;

  let f0h = s0 >>. 51ul in
  FStar.Math.Lemmas.lemma_div_lt (v s0) 64 51;

  let f1l = (s1 &. u64 0x3fffffffff) <<. 13ul in
  mod_mask_lemma s1 38ul;
  uintv_extensionality (mod_mask #U64 38ul) (u64 0x3fffffffff);
  assert_norm (pow2 38 * pow2 13 = pow2 51);
  assert_norm (pow2 51 < pow2 64);
  FStar.Math.Lemmas.modulo_lemma ((v s1 % pow2 38) * pow2 13) (pow2 64);

  let f1h = s1 >>. 38ul in
  FStar.Math.Lemmas.lemma_div_lt (v s1) 64 38;

  let f2l = (s2 &. u64 0x1ffffff) <<. 26ul in
  mod_mask_lemma s2 25ul;
  uintv_extensionality (mod_mask #U64 25ul) (u64 0x1ffffff);
  assert_norm (pow2 25 * pow2 26 = pow2 51);
  FStar.Math.Lemmas.modulo_lemma ((v s2 % pow2 25) * pow2 26) (pow2 64);

  let f2h = s2 >>. 25ul in
  FStar.Math.Lemmas.lemma_div_lt (v s2) 64 25;

  let f3l = (s3 &. u64 0xfff) <<. 39ul in
  mod_mask_lemma s3 12ul;
  uintv_extensionality (mod_mask #U64 12ul) (u64 0xfff);
  assert_norm (pow2 12 * pow2 39 = pow2 51);
  FStar.Math.Lemmas.modulo_lemma ((v s3 % pow2 12) * pow2 39) (pow2 64);

  let f3h = s3 >>. 12ul in

  let f0 = f0l in
  let f1 = f0h |. f1l in
  logor_disjoint f0h f1l 13;
  let f2 = f1h |. f2l in
  logor_disjoint f1h f2l 26;
  let f3 = f2h |. f3l in
  logor_disjoint f2h f3l 39;
  let f4 = f3h in
  let f = (f0, f1, f2, f3, f4) in
  lemma_load_felem_fits5 f u64s;
  lemma_load_felem5 f u64s

val lemma_subtract_p5_0:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> f':felem5
  -> Lemma
    (requires (
      let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
     (v f4 <> 0x7ffffffffffff || v f3 <> 0x7ffffffffffff || v f2 <> 0x7ffffffffffff || v f1 <> 0x7ffffffffffff || v f0 < 0x7ffffffffffed) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4)))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p5_0 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (0x7ffffffffffff = pow2 51 - 1);
  assert_norm (0x7ffffffffffed = pow2 51 - 19);
  assert_norm (pow51 = pow2 51);
  assert (as_nat5 f == v f0 + v f1 * pow51 + v f2 * pow51 * pow51 +
    v f3 * pow51 * pow51 * pow51 + v f4 * pow51 * pow51 * pow51 * pow51);
  assert (as_nat5 f <= pow2 51 - 20 + (pow2 51 - 1) * pow2 51 + (pow2 51 - 1) * pow2 51 * pow2 51 +
    (pow2 51 - 1) * pow2 51 * pow2 51 * pow2 51 + (pow2 51 - 1) * pow2 51 * pow2 51 * pow2 51 * pow2 51);
  assert (as_nat5 f < pow2 255 - 19);
  assert (as_nat5 f == as_nat5 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') prime

val lemma_subtract_p5_1:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> f':felem5
  -> Lemma
    (requires (
      let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
     (v f4 = 0x7ffffffffffff && v f3 = 0x7ffffffffffff && v f2 = 0x7ffffffffffff && v f1 = 0x7ffffffffffff && v f0 >= 0x7ffffffffffed) /\
      (v f0' = v f0 - 0x7ffffffffffed && v f1' = v f1 - 0x7ffffffffffff && v f2' = v f2 - 0x7ffffffffffff &&
       v f3' = v f3 - 0x7ffffffffffff && v f4' = v f4 - 0x7ffffffffffff)))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p5_1 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (0x7ffffffffffff = pow2 51 - 1);
  assert_norm (0x7ffffffffffed = pow2 51 - 19);
  assert_norm (pow51 = pow2 51);
  assert (as_nat5 f' % prime == (v f0' + v f1' * pow51 + v f2' * pow51 * pow51 +
    v f3' * pow51 * pow51 * pow51 + v f4' * pow51 * pow51 * pow51 * pow51) % prime);
  assert (as_nat5 f' % prime ==
    (v f0 - (pow2 51 - 19) + (v f1 - (pow2 51 - 1)) * pow2 51 + (v f2 - (pow2 51 - 1)) * pow2 51 * pow2 51 +
    (v f3 - (pow2 51 - 1)) * pow2 51 * pow2 51 * pow2 51 +
    (v f4 - (pow2 51 - 1)) * pow2 51 * pow2 51 * pow2 51 * pow2 51) % prime);
  assert (as_nat5 f' % prime ==
    (v f0 + v f1 * pow2 51 + v f2 * pow2 51 * pow2 51 +
    v f3 * pow2 51 * pow2 51 * pow2 51 + v f4 * pow2 51 * pow2 51 * pow2 51 * pow2 51 - prime) % prime);
  FStar.Math.Lemmas.lemma_mod_sub (as_nat5 f) 1 prime

val lemma_subtract_p:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> f':felem5
  -> Lemma
    (requires (
      let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
     (((v f4 <> 0x7ffffffffffff || v f3 <> 0x7ffffffffffff || v f2 <> 0x7ffffffffffff || v f1 <> 0x7ffffffffffff || v f0 < 0x7ffffffffffed) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4)) \/
     ((v f4 = 0x7ffffffffffff && v f3 = 0x7ffffffffffff && v f2 = 0x7ffffffffffff && v f1 = 0x7ffffffffffff && v f0 >= 0x7ffffffffffed) /\
      (v f0' = v f0 - 0x7ffffffffffed && v f1' = v f1 - 0x7ffffffffffff && v f2' = v f2 - 0x7ffffffffffff &&
       v f3' = v f3 - 0x7ffffffffffff && v f4' = v f4 - 0x7ffffffffffff)))))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  if ((v f4 <> 0x7ffffffffffff || v f3 <> 0x7ffffffffffff || v f2 <> 0x7ffffffffffff || v f1 <> 0x7ffffffffffff || v f0 < 0x7ffffffffffed) &&
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))
  then lemma_subtract_p5_0 f f'
  else lemma_subtract_p5_1 f f'

val lemma_store_felem2: f:felem5 ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    v f0 + (v f1 % pow2 13) * pow2 51 +
    v f1 / pow2 13 * pow2 64 + (v f2 % pow2 26) * pow2 102 +
    v f2 / pow2 26 * pow2 128 + (v f3 % pow2 39) * pow2 153 +
    v f3 / pow2 39 * pow2 192 + v f4 * pow2 204 ==
    v f0 + v f1 * pow2 51 + v f2 * pow2 102 + v f3 * pow2 153 + v f4 * pow2 204)
let lemma_store_felem2 f =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (pow2 64 = pow2 13 * pow2 51);
  FStar.Math.Lemmas.euclidean_division_definition (v f1) (pow2 13);

  assert_norm (pow2 128 = pow2 26 * pow2 102);
  FStar.Math.Lemmas.euclidean_division_definition (v f2) (pow2 26);

  assert_norm (pow2 192 = pow2 39 * pow2 153);
  FStar.Math.Lemmas.euclidean_division_definition (v f3) (pow2 39)

val lemma_store_felem1: f:felem5 ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    v f0 + (v f1 % pow2 13) * pow2 51 +
    (v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38) * pow2 64 +
    (v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25) * pow2 128 +
    (v f3 / pow2 39 + v f4 * pow2 12) * pow2 192 ==
    v f0 + v f1 * pow2 51 + v f2 * pow2 102 + v f3 * pow2 153 + v f4 * pow2 204)
let lemma_store_felem1 f =
  let (f0, f1, f2, f3, f4) = f in
  assert (
    v f0 + (v f1 % pow2 13) * pow2 51 +
    (v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38) * pow2 64 +
    (v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25) * pow2 128 +
    (v f3 / pow2 39 + v f4 * pow2 12) * pow2 192 ==
    v f0 + (v f1 % pow2 13) * pow2 51 +
    v f1 / pow2 13 * pow2 64 + (v f2 % pow2 26) * pow2 38 * pow2 64 +
    v f2 / pow2 26 * pow2 128 + (v f3 % pow2 39) * pow2 25 * pow2 128 +
    v f3 / pow2 39 * pow2 192 + v f4 * pow2 12 * pow2 192);
  lemma_mul_assos_3 (v f2 % pow2 26) (pow2 38) (pow2 64);
  assert_norm (pow2 38 * pow2 64 = pow2 102);
  assert ((v f2 % pow2 26) * pow2 38 * pow2 64 == (v f2 % pow2 26) * pow2 102);
  lemma_mul_assos_3 (v f3 % pow2 39) (pow2 25) (pow2 128);
  assert_norm (pow2 25 * pow2 128 = pow2 153);
  assert ((v f3 % pow2 39) * pow2 25 * pow2 128 == (v f3 % pow2 39) * pow2 153);
  lemma_mul_assos_3 (v f4) (pow2 12) (pow2 192);
  assert_norm (pow2 12 * pow2 192 = pow2 204);
  assert (v f4 * pow2 12 * pow2 192 == v f4 * pow2 204);
  assert (
    v f0 + (v f1 % pow2 13) * pow2 51 +
    v f1 / pow2 13 * pow2 64 + (v f2 % pow2 26) * pow2 38 * pow2 64 +
    v f2 / pow2 26 * pow2 128 + (v f3 % pow2 39) * pow2 25 * pow2 128 +
    v f3 / pow2 39 * pow2 192 + v f4 * pow2 12 * pow2 192 ==
    v f0 + (v f1 % pow2 13) * pow2 51 +
    v f1 / pow2 13 * pow2 64 + (v f2 % pow2 26) * pow2 102 +
    v f2 / pow2 26 * pow2 128 + (v f3 % pow2 39) * pow2 153 +
    v f3 / pow2 39 * pow2 192 + v f4 * pow2 204);
  lemma_store_felem2 f

val lemma_as_nat1: f:felem5 ->
  Lemma (let (f0, f1, f2, f3, f4) = f in
    as_nat5 f == v f0 + v f1 * pow2 51 + v f2 * pow2 102 + v f3 * pow2 153 + v f4 * pow2 204)
let lemma_as_nat1 f =
  assert_norm (pow51 = pow2 51);
  assert_norm (pow2 51 * pow2 51 = pow2 102);
  assert_norm (pow2 51 * pow2 51 * pow2 51 = pow2 153);
  assert_norm (pow2 51 * pow2 51 * pow2 51 * pow2 51 = pow2 204)

val lemma_store_felem0: f:felem5{felem_fits5 f (1, 1, 1, 1, 1) /\ as_nat5 f < prime} ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    let o0 = v f0 + (v f1 % pow2 13) * pow2 51 in
    let o1 = v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38 in
    let o2 = v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25 in
    let o3 = v f3 / pow2 39 + (v f4 % pow2 52) * pow2 12 in
    as_nat5 f == o0 + o1 * pow2 64 + o2 * pow2 64 * pow2 64 + o3 * pow2 64 * pow2 64 * pow2 64)
let lemma_store_felem0 f =
  assert_norm (pow51 = pow2 51);
  let (f0, f1, f2, f3, f4) = f in
  let o0 = v f0 + (v f1 % pow2 13) * pow2 51 in
  let o1 = v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38 in
  let o2 = v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25 in
  let o3 = v f3 / pow2 39 + (v f4 % pow2 52) * pow2 12 in
  assert_norm (pow2 51 < pow2 52);
  FStar.Math.Lemmas.modulo_lemma (v f4) (pow2 52);
  assert (v f4 % pow2 52 = v f4);
  assert (
    o0 + o1 * pow2 64 + o2 * pow2 64 * pow2 64 + o3 * pow2 64 * pow2 64 * pow2 64 ==
    v f0 + (v f1 % pow2 13) * pow2 51 +
    (v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38) * pow2 64 +
    (v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25) * pow2 64 * pow2 64 +
    (v f3 / pow2 39 + v f4 * pow2 12) * pow2 64 * pow2 64 * pow2 64);
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert (
    o0 + o1 * pow2 64 + o2 * pow2 64 * pow2 64 + o3 * pow2 64 * pow2 64 * pow2 64 ==
    v f0 + (v f1 % pow2 13) * pow2 51 +
    (v f1 / pow2 13 + (v f2 % pow2 26) * pow2 38) * pow2 64 +
    (v f2 / pow2 26 + (v f3 % pow2 39) * pow2 25) * pow2 128 +
    (v f3 / pow2 39 + v f4 * pow2 12) * pow2 192);
  lemma_store_felem1 f;
  lemma_as_nat1 f

val lemma_store_felem: f:felem5{felem_fits5 f (1, 1, 1, 1, 1) /\ as_nat5 f < prime} ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    let o0 = f0 |. (f1 <<. 51ul) in
    let o1 = (f1 >>. 13ul) |. (f2 <<. 38ul) in
    let o2 = (f2 >>. 26ul) |. (f3 <<. 25ul) in
    let o3 = (f3 >>. 39ul) |. (f4 <<. 12ul) in
    as_nat5 f == v o0 + v o1 * pow2 64 + v o2 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64)
let lemma_store_felem f =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (pow51 = pow2 51);
  let o0 = f0 |. (f1 <<. 51ul) in
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f1) 64 51;
  logor_disjoint f0 (f1 <<. 51ul) 51;

  let o1 = (f1 >>. 13ul) |. (f2 <<. 38ul) in
  FStar.Math.Lemmas.lemma_div_lt (v f1) 51 13;
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f2) 64 38;
  FStar.Math.Lemmas.multiple_modulo_lemma (v f2 % pow2 26) (pow2 38);
  logor_disjoint (f1 >>. 13ul) (f2 <<. 38ul) 38;

  let o2 = (f2 >>. 26ul) |. (f3 <<. 25ul) in
  FStar.Math.Lemmas.lemma_div_lt (v f2) 51 26;
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f3) 64 25;
  FStar.Math.Lemmas.multiple_modulo_lemma (v f3 % pow2 39) (pow2 25);
  logor_disjoint (f2 >>. 26ul) (f3 <<. 25ul) 25;

  let o3 = (f3 >>. 39ul) |. (f4 <<. 12ul) in
  FStar.Math.Lemmas.lemma_div_lt (v f3) 51 39;
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 64 12;
  FStar.Math.Lemmas.multiple_modulo_lemma (v f4 % pow2 52) (pow2 12);
  logor_disjoint (f3 >>. 39ul) (f4 <<. 12ul) 12;
  lemma_store_felem0 f

val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
      let dummy = mask &. (p1 ^. p2) in
      let p1' = p1 ^. dummy in
      let p2' = p2 ^. dummy in
      if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)
let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0);
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1

#push-options "--max_fuel 0 --max_ifuel 0"
val mul64_wide_add3_lemma:
  #m0:scale64 -> #m1:scale64 -> #m2:scale64
 -> #m3:scale64 -> #m4:scale64 -> #m5:scale64
 -> a0:uint64{felem_fits1 a0 m0}
 -> a1:uint64{felem_fits1 a1 m1}
 -> b0:uint64{felem_fits1 b0 m2}
 -> b1:uint64{felem_fits1 b1 m3}
 -> c0:uint64{felem_fits1 c0 m4}
 -> c1:uint64{felem_fits1 c1 m5}
 -> Lemma
   (requires m0 * m1 + m2 * m3 + m4 * m5 < pow2 13)
   (ensures
     v a0 * v a1 + v b0 * v b1 + v c0 * v c1 < pow2 128 /\
     (v a0 * v a1 + v b0 * v b1 + v c0 * v c1) <=
      (m0 * m1 + m2 * m3 + m4 * m5) * max51 * max51)
let mul64_wide_add3_lemma #m0 #m1 #m2 #m3 #m4 #m5 a0 a1 b0 b1 c0 c1 =
  assert (pow51 = pow2 51);
  lemma_mul_le (v a0) (m0 * max51) (v a1) (m1 * max51);
  lemma_mul_le (v b0) (m2 * max51) (v b1) (m3 * max51);
  lemma_mul_le (v c0) (m4 * max51) (v c1) (m5 * max51);
  lemma_add_le (v a0 * v a1) (m0 * max51 * m1 * max51) (v b0 * v b1) (m2 * max51 * m3 * max51);
  lemma_add_le (v a0 * v a1 + v b0 * v b1) (m0 * max51 * m1 * max51 + m2 * max51 * m3 * max51)
    (v c0 * v c1) (m4 * max51 * m5 * max51);

  assert (v a0 * v a1 + v b0 * v b1 + v c0 * v c1 <=
    m0 * max51 * m1 * max51 + m2 * max51 * m3 * max51 + m4 * max51 * m5 * max51);
  assert_by_tactic (m0 * max51 * m1 * max51 + m2 * max51 * m3 * max51 + m4 * max51 * m5 * max51 ==
    (m0 * m1 + m2 * m3 + m4 * m5) * max51 * max51) canon;
  assert_norm (pow2 13 > 0);
  lemma_mul_le (m0 * m1 + m2 * m3 + m4 * m5) (pow2 13 - 1) (max51 * max51) (max51 * max51);
  assert ((m0 * m1 + m2 * m3 + m4 * m5) * max51 * max51 < pow2 13 * max51 * max51);
  assert (v a0 * v a1 + v b0 * v b1 + v c0 * v c1 < pow2 13 * max51 * max51);
  assert_norm (pow2 13 * pow2 51 * pow2 51 = pow2 115);
  assert_norm (pow2 115 < pow2 128)
#pop-options

val lemma_fmul_fsqr50: f0:nat -> f1:nat -> f2:nat -> f3:nat -> f4:nat ->
  Lemma
   (f0 * f0 + f1 * f4 * 19 + f2 * f3 * 19 + f3 * f2 * 19 + f4 * f1 * 19 ==
    f0 * f0 + 38 * f4 * f1 + 38 * f2 * f3)
let lemma_fmul_fsqr50 f0 f1 f2 f3 f4 = ()

val lemma_fmul_fsqr51: f0:nat -> f1:nat -> f2:nat -> f3:nat -> f4:nat ->
  Lemma
   (f0 * f1 * pow51 + f1 * f0 * pow51 + f2 * f4 * 19 * pow51 +
   f3 * f3 * 19 * pow51 + f4 * f2 * 19 * pow51 ==
   (2 * f0 * f1 + 38 * f4 * f2 + 19 * f3 * f3) * pow51)
let lemma_fmul_fsqr51 f0 f1 f2 f3 f4 = ()

val lemma_fmul_fsqr52: f0:nat -> f1:nat -> f2:nat -> f3:nat -> f4:nat ->
  Lemma
   (f0 * f2 * pow51 * pow51 + f1 * f1 * pow51 * pow51 + f2 * f0 * pow51 * pow51 +
   f3 * f4 * 19 * pow51 * pow51 + f4 * f3 * 19 * pow51 * pow51 ==
   (2 * f0 * f2 + f1 * f1 + 38 * f4 * f3) * pow51 * pow51)
let lemma_fmul_fsqr52 f0 f1 f2 f3 f4 = ()

val lemma_fmul_fsqr53: f0:nat -> f1:nat -> f2:nat -> f3:nat -> f4:nat ->
  Lemma
   (f0 * f3 * pow51 * pow51 * pow51 + f1 * f2 * pow51 * pow51 * pow51 +
   f2 * f1 * pow51 * pow51 * pow51 + f3 * f0 * pow51 * pow51 * pow51 +
   f4 * f4 * 19 * pow51 * pow51 * pow51 ==
   (2 * f0 * f3 + 2 * f1 * f2 + 19 * f4 * f4) * pow51 * pow51 * pow51)
let lemma_fmul_fsqr53 f0 f1 f2 f3 f4 = ()

val lemma_fmul_fsqr54: f0:nat -> f1:nat -> f2:nat -> f3:nat -> f4:nat ->
  Lemma
   (f0 * f4 * pow51 * pow51 * pow51 * pow51 + f1 * f3 * pow51 * pow51 * pow51 * pow51 +
   f2 * f2 * pow51 * pow51 * pow51 * pow51 + f3 * f1 * pow51 * pow51 * pow51 * pow51 +
   f4 * f0 * pow51 * pow51 * pow51 * pow51 ==
   (2 * f0 * f4 + 2 * f1 * f3 + f2 * f2) * pow51 * pow51 * pow51 * pow51)
let lemma_fmul_fsqr54 f0 f1 f2 f3 f4 = ()

val lemma_fmul_fsqr5: f:felem5{felem_fits5 f (9, 10, 9, 9, 9)} ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    let s0 = v f0 * v f0 + 38 * v f4 * v f1 + 38 * v f2 * v f3 in
    let s1 = 2 * v f0 * v f1 + 38 * v f4 * v f2 + 19 * v f3 * v f3 in
    let s2 = 2 * v f0 * v f2 + v f1 * v f1 + 38 * v f4 * v f3 in
    let s3 = 2 * v f0 * v f3 + 2 * v f1 * v f2 + 19 * v f4 * v f4 in
    let s4 = 2 * v f0 * v f4 + 2 * v f1 * v f3 + v f2 * v f2 in
    fmul (feval f) (feval f) == (s0 + s1 * pow51 + s2 * pow51 * pow51 +
      s3 * pow51 * pow51 * pow51 + s4 * pow51 * pow51 * pow51 * pow51) % prime)
let lemma_fmul_fsqr5 f =
  let (f0, f1, f2, f3, f4) = f in
  lemma_fmul5 f f;
  lemma_smul_felem5 f0 (f0, f1, f2, f3, f4);
  lemma_smul_felem5 f1 (f4 *! u64 19, f0, f1, f2, f3);
  lemma_mul_assos_3 (v f1) (v f4) 19;
  lemma_smul_felem5 f2 (f3 *! u64 19, f4 *! u64 19, f0, f1, f2);
  lemma_mul_assos_3 (v f2) (v f3) 19;
  lemma_mul_assos_3 (v f2) (v f4) 19;
  lemma_smul_felem5 f3 (f2 *! u64 19, f3 *! u64 19, f4 *! u64 19, f0, f1);
  lemma_mul_assos_3 (v f3) (v f2) 19;
  lemma_mul_assos_3 (v f3) (v f3) 19;
  lemma_mul_assos_3 (v f3) (v f4) 19;
  lemma_smul_felem5 f4 (f1 *! u64 19, f2 *! u64 19, f3 *! u64 19, f4 *! u64 19, f0);
  lemma_mul_assos_3 (v f4) (v f1) 19;
  lemma_mul_assos_3 (v f4) (v f2) 19;
  lemma_mul_assos_3 (v f4) (v f3) 19;
  lemma_mul_assos_3 (v f4) (v f4) 19;

  lemma_fmul_fsqr50 (v f0) (v f1) (v f2) (v f3) (v f4);
  lemma_fmul_fsqr51 (v f0) (v f1) (v f2) (v f3) (v f4);
  lemma_fmul_fsqr52 (v f0) (v f1) (v f2) (v f3) (v f4);
  lemma_fmul_fsqr53 (v f0) (v f1) (v f2) (v f3) (v f4);
  lemma_fmul_fsqr54 (v f0) (v f1) (v f2) (v f3) (v f4)
