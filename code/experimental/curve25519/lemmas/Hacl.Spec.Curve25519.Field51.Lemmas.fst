module Hacl.Spec.Curve25519.Field51.Lemmas

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul
open NatPrime

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

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

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

#set-options "--z3rlimit 300"

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

#set-options "--z3rlimit 150"

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

val lemma_carry51:
    l:uint64
  -> cin:uint64
  -> Lemma
    (requires v l + v cin < pow2 64)
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

val lemma_carry_wide5_simplify:
  inp:felem_wide5{felem_wide_fits5 inp (6579, 4797, 3340, 1881, 423)} ->
  c0:uint64 -> c1:uint64 -> c2:uint64 -> c3:uint64 -> c4:uint64 ->
  t0:uint64 -> t1:uint64 -> t2:uint64 -> t3:uint64 -> t4:uint64 ->
  Lemma
    (requires
    feval_wide inp ==
    (v c0 * pow2 51 + v t0 +
    (v c1 * pow2 51 + v t1 - v c0) * pow51 +
    (v c2 * pow2 51 + v t2 - v c1) * pow51 * pow51 +
    (v c3 * pow2 51 + v t3 - v c2) * pow51 * pow51 * pow51 +
    (v c4 * pow2 51 + v t4 - v c3) * pow51 * pow51 * pow51 * pow51) % prime)
   (ensures
    feval_wide inp ==
    (v t0 + v c4 * 19 + v t1 * pow51 + v t2 * pow51 * pow51 +
     v t3 * pow51 * pow51 * pow51 + v t4 * pow51 * pow51 * pow51 * pow51) % prime)
let lemma_carry_wide5_simplify inp c0 c1 c2 c3 c4 t0 t1 t2 t3 t4 =
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

val lemma_smul_felem5:
    #m1:scale64
  -> #m2:scale64_5
  -> u1:uint64{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2 /\ m1 *^ m2 <=* s128x5 67108864}
  -> Lemma (let (f20, f21, f22, f23, f24) = f2 in
      v u1 * as_nat5 f2 == v u1 * v f20 + v u1 * v f21 * pow51 +
      v u1 * v f22 * pow51 * pow51 + v u1 * v f23 * pow51 * pow51 * pow51 +
      v u1 * v f24 * pow51 * pow51 * pow51 * pow51)
let lemma_smul_felem5 #m1 #m2 u1 f2 =
  let (f20, f21, f22, f23, f24) = f2 in
  assert (v u1 * as_nat5 f2 == v u1 * (v f20 + v f21 * pow51 + v f22 * pow51 * pow51 +
    v f23 * pow51 * pow51 * pow51 + v f24 * pow51 * pow51 * pow51 * pow51));
  lemma_mul5_distr_l (v u1) (v f20) (v f21 * pow51) (v f22 * pow51 * pow51)
    (v f23 * pow51 * pow51 * pow51) (v f24 * pow51 * pow51 * pow51 * pow51)


val lemma_smul_add_felem5:
    #m1:scale64
  -> #m2:scale64_5
  -> #m3:scale128_5
  -> u1:uint64{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s128x5 67108864}
  -> Lemma (let (f20, f21, f22, f23, f24) = f2 in
      let (o0, o1, o2, o3, o4) = acc1 in
      wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 ==
      v o0 + v o1 * pow51 + v o2 * pow51 * pow51 +
      v o3 * pow51 * pow51 * pow51 + v o4 * pow51 * pow51 * pow51 * pow51 +
      v u1 * v f20 + v u1 * v f21 * pow51 +
      v u1 * v f22 * pow51 * pow51 + v u1 * v f23 * pow51 * pow51 * pow51 +
      v u1 * v f24 * pow51 * pow51 * pow51 * pow51)
let lemma_smul_add_felem5 #m1 #m2 #m3 u1 f2 acc1 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (o0, o1, o2, o3, o4) = acc1 in
  assert (wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 ==
    v o0 + v o1 * pow51 + v o2 * pow51 * pow51 +
    v o3 * pow51 * pow51 * pow51 + v o4 * pow51 * pow51 * pow51 * pow51 +
    v u1 * (v f20 + v f21 * pow51 + v f22 * pow51 * pow51 +
    v f23 * pow51 * pow51 * pow51 + v f24 * pow51 * pow51 * pow51 * pow51));
  lemma_mul5_distr_l (v u1) (v f20) (v f21 * pow51) (v f22 * pow51 * pow51)
    (v f23 * pow51 * pow51 * pow51) (v f24 * pow51 * pow51 * pow51 * pow51)
