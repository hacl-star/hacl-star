module Hacl.Spec.Poly.Lemmas0

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Poly

module S = Spec.Poly

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mult_le: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a <= b /\ c <= d)
  (ensures  a * c <= b * d)
let lemma_mult_le a b c d = ()

val lemma_mul5_distr_l: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_prime: unit -> Lemma (pow2 130 % S.prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % S.prime = 5 % S.prime);
  assert_norm (5 < S.prime);
  Math.Lemmas.small_mod 5 S.prime


val lemma_mul5_distr_l_pow: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  (a * (b + c * pow26 + d * pow52 + e * pow78 + f * pow104) ==
   a * b + a * c * pow26 + a * d * pow52 + a * e * pow78 + a * f * pow104)

let lemma_mul5_distr_l_pow a b c d e f =
  calc (==) {
    a * (b + c * pow26 + d * pow52 + e * pow78 + f * pow104);
    (==) { lemma_mul5_distr_l a b (c * pow26) (d * pow52) (e * pow78) (f * pow104) }
    a * b + a * (c * pow26) + a * (d * pow52) + a * (e * pow78) + a * (f * pow104);
    (==) {
      Math.Lemmas.paren_mul_right a c pow26;
      Math.Lemmas.paren_mul_right a d pow52;
      Math.Lemmas.paren_mul_right a e pow78;
      Math.Lemmas.paren_mul_right a f pow104 }
    a * b + a * c * pow26 + a * d * pow52 + a * e * pow78 + a * f * pow104;
    }


val lemma_mul5_distr_l_pow_pow26_mod: b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  ((b + c * pow26 + d * pow52 + e * pow78 + f * pow104) * pow26 % S.prime ==
   (f * 5 + b * pow26 + c * pow52 + d * pow78 + e * pow104) % S.prime)

let lemma_mul5_distr_l_pow_pow26_mod b c d e f =
  calc (==) {
    (b + c * pow26 + d * pow52 + e * pow78 + f * pow104) * pow26 % S.prime;
    (==) { }
    (b * pow26 + c * pow26 * pow26 + d * pow52 * pow26 +
    e * pow78 * pow26 + f * pow104 * pow26) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right c pow26 pow26;
      Math.Lemmas.paren_mul_right d pow52 pow26;
      Math.Lemmas.paren_mul_right e pow78 pow26;
      Math.Lemmas.paren_mul_right f pow104 pow26 }
    (b * pow26 + c * (pow26 * pow26) + d * (pow52 * pow26) +
    e * (pow78 * pow26) + f * (pow104 * pow26)) % S.prime;
    (==) {
      assert_norm (pow26 * pow26 = pow52);
      assert_norm (pow52 * pow26 = pow78);
      assert_norm (pow78 * pow26 == pow104);
      assert_norm (pow104 * pow26 == pow2 130) }
    (b * pow26 + c * pow52 + d * pow78 + e * pow104 + f * pow2 130) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (b * pow26 + c * pow52 + d * pow78 + e * pow104) (f * pow2 130) S.prime }
    (b * pow26 + c * pow52 + d * pow78 + e * pow104 + (f * pow2 130 % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r f (pow2 130) S.prime; lemma_prime () }
    (b * pow26 + c * pow52 + d * pow78 + e * pow104 + (f * 5 % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (b * pow26 + c * pow52 + d * pow78 + e * pow104) (f * 5) S.prime }
    (b * pow26 + c * pow52 + d * pow78 + e * pow104 + f * 5) % S.prime;
    }


val lemma_mul5_distr_l_pow_pow52_mod: b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  ((b + c * pow26 + d * pow52 + e * pow78 + f * pow104) * pow52 % S.prime ==
   (e * 5 + f * 5 * pow26 + b * pow52 + c * pow78 + d * pow104) % S.prime)

let lemma_mul5_distr_l_pow_pow52_mod b c d e f =
  let s1 = b + c * pow26 + d * pow52 + e * pow78 + f * pow104 in
  let s2 = b * pow26 + c * pow52 + d * pow78 + e * pow104 + f * 5 in
  calc (==) {
    s1 * pow52 % S.prime;
    (==) { assert_norm (pow26 * pow26 = pow52) }
    s1 * pow26 * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (s1 * pow26) pow26 S.prime }
    (s1 * pow26 % S.prime) * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow26_mod b c d e f }
    (s2 % S.prime) * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l s2 pow26 S.prime }
    s2 * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow26_mod (5 * f) b c d e }
    (e * 5 + f * 5 * pow26 + b * pow52 + c * pow78 + d * pow104) % S.prime;
    }


val lemma_mul5_distr_l_pow_pow78_mod: b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  ((b + c * pow26 + d * pow52 + e * pow78 + f * pow104) * pow78 % S.prime ==
   (d * 5 + e * 5 * pow26 + f * 5 * pow52 + b * pow78 + c * pow104) % S.prime)

let lemma_mul5_distr_l_pow_pow78_mod b c d e f =
  let s1 = b + c * pow26 + d * pow52 + e * pow78 + f * pow104 in
  let s2 = e * 5 + f * 5 * pow26 + b * pow52 + c * pow78 + d * pow104 in
  calc (==) {
    s1 * pow78 % S.prime;
    (==) { assert_norm (pow52 * pow26 = pow78) }
    s1 * pow52 * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (s1 * pow52) pow26 S.prime }
    (s1 * pow52 % S.prime) * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow52_mod b c d e f }
    (s2 % S.prime) * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l s2 pow26 S.prime }
    s2 * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow26_mod (5 * e) (5 * f) b c d }
    (d * 5 + e * 5 * pow26 + f * 5 * pow52 + b * pow78 + c * pow104) % S.prime;
    }


val lemma_mul5_distr_l_pow_pow104_mod: b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  ((b + c * pow26 + d * pow52 + e * pow78 + f * pow104) * pow104 % S.prime ==
   (c * 5 + d * 5 * pow26 + e * 5 * pow52 + f * 5 * pow78 + b * pow104) % S.prime)

let lemma_mul5_distr_l_pow_pow104_mod b c d e f =
  let s1 = b + c * pow26 + d * pow52 + e * pow78 + f * pow104 in
  let s2 = d * 5 + e * 5 * pow26 + f * 5 * pow52 + b * pow78 + c * pow104 in
  calc (==) {
    s1 * pow104 % S.prime;
    (==) { assert_norm (pow78 * pow26 = pow104) }
    s1 * pow78 * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (s1 * pow78) pow26 S.prime }
    (s1 * pow78 % S.prime) * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow78_mod b c d e f }
    (s2 % S.prime) * pow26 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l s2 pow26 S.prime }
    s2 * pow26 % S.prime;
    (==) { lemma_mul5_distr_l_pow_pow26_mod (5 * d) (5 * e) (5 * f) b c }
    (c * 5 + d * 5 * pow26 + e * 5 * pow52 + f * 5 * pow78 + b * pow104) % S.prime;
    }


val lemma_mod3: a:nat -> b:nat -> c:nat -> d:nat -> p:pos -> Lemma
  (requires a * c % p == d % p)
  (ensures  a * b * c % p == b * d % p)

let lemma_mod3 a b c d p =
  calc (==) {
    a * b * c % p;
    (==) { Math.Lemmas.paren_mul_right b a c }
    b * (a * c) % p;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r b (a * c) p }
    b * (a * c % p) % p;
    (==) { assert (a * c % p == d % p) }
    b * (d % p) % p;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r b d p }
    b * d % p;
    }


val mul5_nat_lemma0: c:uint64 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 r (1, 1, 1, 1, 1) /\
    r5 == precomp_r5 r)
  (ensures
   (let (r0, r1, r2, r3, r4) = r in
    let (r50, r51, r52, r53, r54) = r5 in
    as_nat5 r * v c * pow26 % S.prime ==
    v c * as_nat5 (r54,r0,r1,r2,r3) % S.prime))

let mul5_nat_lemma0 c r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (r50, r51, r52, r53, r54) = r5 in
  let c0 = (r54,r0,r1,r2,r3) in
  lemma_mul5_distr_l_pow_pow26_mod (v r0) (v r1) (v r2) (v r3) (v r4);
  lemma_mod3 (as_nat5 r) (v c) pow26 (as_nat5 c0) S.prime


val mul5_nat_lemma1: c:uint64 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 r (1, 1, 1, 1, 1) /\
    r5 == precomp_r5 r)
  (ensures
   (let (r0, r1, r2, r3, r4) = r in
    let (r50, r51, r52, r53, r54) = r5 in
    as_nat5 r * v c * pow52 % S.prime ==
    v c * as_nat5 (r53,r54,r0,r1,r2) % S.prime))

let mul5_nat_lemma1 c r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (r50, r51, r52, r53, r54) = r5 in
  let c1 = (r53,r54,r0,r1,r2) in
  lemma_mul5_distr_l_pow_pow52_mod (v r0) (v r1) (v r2) (v r3) (v r4);
  lemma_mod3 (as_nat5 r) (v c) pow52 (as_nat5 c1) S.prime


val mul5_nat_lemma2: c:uint64 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 r (1, 1, 1, 1, 1) /\
    r5 == precomp_r5 r)
  (ensures
   (let (r0, r1, r2, r3, r4) = r in
    let (r50, r51, r52, r53, r54) = r5 in
    as_nat5 r * v c * pow78 % S.prime ==
    v c * as_nat5 (r52,r53,r54,r0,r1) % S.prime))

let mul5_nat_lemma2 c r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (r50, r51, r52, r53, r54) = r5 in
  let c2 = (r52,r53,r54,r0,r1) in
  lemma_mul5_distr_l_pow_pow78_mod (v r0) (v r1) (v r2) (v r3) (v r4);
  lemma_mod3 (as_nat5 r) (v c) pow78 (as_nat5 c2) S.prime


val mul5_nat_lemma3: c:uint64 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 r (1, 1, 1, 1, 1) /\
    r5 == precomp_r5 r)
  (ensures
   (let (r0, r1, r2, r3, r4) = r in
    let (r50, r51, r52, r53, r54) = r5 in
    as_nat5 r * v c * pow104 % S.prime ==
    v c * as_nat5 (r51,r52,r53,r54,r0) % S.prime))

let mul5_nat_lemma3 c r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (r50, r51, r52, r53, r54) = r5 in
  let c3 = (r51,r52,r53,r54,r0) in
  lemma_mul5_distr_l_pow_pow104_mod (v r0) (v r1) (v r2) (v r3) (v r4);
  lemma_mod3 (as_nat5 r) (v c) pow104 (as_nat5 c3) S.prime


val mul5_nat_lemma: f1:felem5 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 r (1, 1, 1, 1, 1) /\
    r5 == precomp_r5 r)
  (ensures
   (let (r0, r1, r2, r3, r4) = r in
    let (f10, f11, f12, f13, f14) = f1 in
    let (r50, r51, r52, r53, r54) = r5 in

   (v f10 * as_nat5 (r0,r1,r2,r3,r4) +
    v f11 * as_nat5 (r54,r0,r1,r2,r3) +
    v f12 * as_nat5 (r53,r54,r0,r1,r2) +
    v f13 * as_nat5 (r52,r53,r54,r0,r1) +
    v f14 * as_nat5 (r51,r52,r53,r54,r0)) % S.prime ==
    feval5 f1 * feval5 r % S.prime))

let mul5_nat_lemma f1 r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let c0 = (r54,r0,r1,r2,r3) in
  let c1 = (r53,r54,r0,r1,r2) in
  let c2 = (r52,r53,r54,r0,r1) in
  let c3 = (r51,r52,r53,r54,r0) in

  let s0 = as_nat5 r * v f10 + as_nat5 r * v f12 * pow52 + as_nat5 r * v f13 * pow78 + as_nat5 r * v f14 * pow104 in
  let s1 = as_nat5 r * v f10 + v f11 * as_nat5 c0 + as_nat5 r * v f13 * pow78 + as_nat5 r * v f14 * pow104 in
  let s2 = as_nat5 r * v f10 + v f11 * as_nat5 c0 + v f12 * as_nat5 c1 + as_nat5 r * v f14 * pow104 in
  let s3 = as_nat5 r * v f10 + v f11 * as_nat5 c0 + v f12 * as_nat5 c1 + v f13 * as_nat5 c2 in

  calc (==) {
    feval5 f1 * feval5 r % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 f1) (feval5 r) S.prime }
    as_nat5 f1 * feval5 r % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (as_nat5 f1) (as_nat5 r) S.prime }
    as_nat5 f1 * as_nat5 r % S.prime;
    (==) { }
    as_nat5 r * (v f10 + v f11 * pow26 + v f12 * pow52 + v f13 * pow78 + v f14 * pow104) % S.prime;
    (==) { lemma_mul5_distr_l_pow (as_nat5 r) (v f10) (v f11) (v f12) (v f13) (v f14) }
    (as_nat5 r * v f11 * pow26 + s0) % S.prime;
    (==) {
      Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 r * v f11 * pow26) s0 S.prime;
      mul5_nat_lemma0 f11 r r5;
      Math.Lemmas.lemma_mod_plus_distr_l (v f11 * as_nat5 c0) s0 S.prime }
    (v f11 * as_nat5 c0 + s0) % S.prime;
    (==) { }
    (as_nat5 r * v f12 * pow52 + s1) % S.prime;
    (==) {
      Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 r * v f12 * pow52) s1 S.prime;
      mul5_nat_lemma1 f12 r r5;
      Math.Lemmas.lemma_mod_plus_distr_l (v f12 * as_nat5 c1) s1 S.prime }
    (v f12 * as_nat5 c1 + s1) % S.prime;
    (==) { }
    (as_nat5 r * v f13 * pow78 + s2) % S.prime;
    (==) {
      Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 r * v f13 * pow78) s2 S.prime;
      mul5_nat_lemma2 f13 r r5;
      Math.Lemmas.lemma_mod_plus_distr_l (v f13 * as_nat5 c2) s2 S.prime }
    (v f13 * as_nat5 c2 + s2) % S.prime;
    (==) { }
    (as_nat5 r * v f14 * pow104 + s3) % S.prime;
    (==) {
      Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 r * v f14 * pow104) s3 S.prime;
      mul5_nat_lemma3 f14 r r5;
      Math.Lemmas.lemma_mod_plus_distr_l (v f14 * as_nat5 c3) s3 S.prime }
    (v f14 * as_nat5 c3 + s3) % S.prime;
    }


val carry_wide_felem5_nat_lemma: f:felem_wide5
  -> c0:uint64 -> c1:uint64 -> c2:uint64 -> c3:uint64 -> c4:uint64 -> c5:uint64 ->
  Lemma (let (i0, i1, i2, i3, i4) = f in
   ((v i0 - v c0 * pow26 + v c4 * 5 - v c5 * pow26) +
    (v i1 + v c0 - v c1 * pow26 + v c5) * pow26 +
    (v i2 + v c1 - v c2 * pow26) * pow52 +
    (v i3 + v c2 - v c3 * pow26) * pow78 +
    (v i4 + v c3 - v c4 * pow26) * pow104) % S.prime == feval5 f)

let carry_wide_felem5_nat_lemma f c0 c1 c2 c3 c4 c5 =
  let (i0, i1, i2, i3, i4) = f in
  calc (==) {
    ((v i0 - v c0 * pow26 + v c4 * 5 - v c5 * pow26) +
    (v i1 + v c0 - v c1 * pow26 + v c5) * pow26 +
    (v i2 + v c1 - v c2 * pow26) * pow52 +
    (v i3 + v c2 - v c3 * pow26) * pow78 +
    (v i4 + v c3 - v c4 * pow26) * pow104) % S.prime;
    (==) { }
    (as_nat5 f + v c4 * 5 - v c1 * pow26 * pow26 +
    v c1 * pow52 - v c2 * pow26 * pow52 +
    v c2 * pow78 - v c3 * pow26 * pow78 +
    v c3 * pow104 - v c4 * pow26 * pow104) % S.prime;
    (==) {
      assert_norm (pow26 * pow26 = pow52);
      assert_norm (pow26 * pow52 = pow78);
      assert_norm (pow26 * pow78 = pow104);
      assert_norm (pow26 * pow104 = pow2 130) }
    (as_nat5 f + v c4 * 5 - v c4 * pow2 130) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (as_nat5 f + v c4 * 5) (v c4 * pow2 130) S.prime }
    (as_nat5 f + v c4 * 5 - (v c4 * pow2 130 % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (v c4) (pow2 130) S.prime; lemma_prime () }
    (as_nat5 f + v c4 * 5 - (v c4 * 5 % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (as_nat5 f + v c4 * 5) (v c4 * 5) S.prime }
    as_nat5 f % S.prime;
    }
