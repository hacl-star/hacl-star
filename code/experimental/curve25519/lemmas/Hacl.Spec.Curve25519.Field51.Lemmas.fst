module Hacl.Spec.Curve25519.Field51.Lemmas

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul

open Hacl.Spec.Curve25519.Field51.Definition

#reset-options "--z3rlimit 20 --using_facts_from '* -FStar.Seq'"

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
  FStar.Math.Lemmas.lemma_mod_plus (feval f1) 8 prime;
  assert (feval out == (v f10 + v f11 * pow51 +
    v f12 * pow51 * pow51 + v f13 * pow51 * pow51 * pow51 +
    v f14 * pow51 * pow51 * pow51 * pow51) % prime);
  // assert_spinoff ((v f10 + v f11 * pow51 +
  //   v f12 * pow51 * pow51 + v f13 * pow51 * pow51 * pow51 +
  //   v f14 * pow51 * pow51 * pow51 * pow51) % prime == feval f1);
  assert_spinoff (feval out == feval f1)

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

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
    (as_nat5 f1 * as_nat5 r) % prime ==
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
  lemma_fmul5_4 f1 r
