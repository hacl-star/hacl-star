module Hacl.Spec.Curve25519.Field64.Lemmas

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul

open Hacl.Spec.Curve25519.Field64.Definition

#reset-options "--z3rlimit 20 --using_facts_from '* -FStar.Seq'"

val lemma_mul_lt: a:nat -> b:nat -> c:pos -> d:pos
  -> Lemma
    (requires a < c /\ b < d)
    (ensures a * b < c * d)
let lemma_mul_lt a b c d = ()

val lemma_mul_assos_5:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat ->
  Lemma (a * b * c * d * e == a * (b * c * d * e))
let lemma_mul_assos_5 a b c d e = ()

val lemma_mod_sub_distr: a:int -> b:int -> n:pos ->
  Lemma ((a - b % n) % n = (a - b) % n)
let lemma_mod_sub_distr a b n =
  FStar.Math.Lemmas.lemma_div_mod b n;
  FStar.Math.Lemmas.distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  FStar.Math.Lemmas.lemma_mod_plus (a - (b % n)) (-(b / n)) n


val lemma_prime: unit ->
  Lemma (pow2 256 % prime == 38)
let lemma_prime () =
  assert_norm (pow2 256 = 2 * pow2 255);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 255) prime;
  //assert (pow2 256 % prime == (2 * (pow2 255 % prime)) % prime);
  assert_norm (pow2 255 % prime = 19 % prime);
  assert_norm (19 < prime);
  FStar.Math.Lemmas.modulo_lemma 19 prime;
  //assert (pow2 256 % prime == (2 * 19) % prime);
  assert_norm (38 < prime);
  FStar.Math.Lemmas.modulo_lemma 38 prime

val lemma_as_nat4: f:felem4
  -> Lemma (as_nat4 f < pow2 256)
let lemma_as_nat4 f =
  let (f0, f1, f2, f3) = f in
  assert (as_nat4 f == v f0 + v f1 * pow2 64 +
    v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 - 1 + (pow2 64 - 1) * pow2 64 +
    (pow2 64 - 1) * pow2 64 * pow2 64 + (pow2 64 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)

val lemma_mul_pow256_add: f:felem4 -> c:uint64
  -> Lemma ((as_nat4 f + v c * pow2 256) % prime == (as_nat4 f + v c * 38) % prime)
let lemma_mul_pow256_add f c =
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f) (v c * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c) (pow2 256) prime;
  lemma_prime ();
  assert ((v c * pow2 256) % prime == (v c * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f) (v c * 38) prime

val lemma_mul_felem_u64: f:felem4 -> u:uint64
  -> Lemma (let (f0, f1, f2, f3) = f in
    as_nat4 f * v u ==
    v f0 * v u +
    v f1 * v u * pow2 64  +
    v f2 * v u * pow2 64 * pow2 64 +
    v f3 * v u * pow2 64 * pow2 64 * pow2 64)
let lemma_mul_felem_u64 f u = ()

val lemma_mul1: f:felem4 -> u:uint64
  -> Lemma (as_nat4 f * v u < pow2 320)
let lemma_mul1 f u =
  lemma_as_nat4 f;
  assert_norm (pow2 256 > 0);
  assert_norm (pow2 64 > 0);
  lemma_mul_lt (as_nat4 f) (v u) (pow2 256) (pow2 64);
  assert_norm (pow2 256 * pow2 64 = pow2 320)

val lemma_mul1_no_carry:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 320}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 64)
let lemma_mul1_no_carry a b c =
  assert_norm (pow2 320 > 0);
  assert (a + c * pow2 256 < pow2 320);
  assert_norm (pow2 64 * pow2 256 = pow2 320)

val lemma_mul1_simplify:
    out:felem4 -> f:felem4 -> u:uint64
  -> h3:uint64 -> c2:uint64
  -> Lemma
    (requires (let (f0, f1, f2, f3) = f in
      as_nat4 out ==
      v f0 * v u +
      v f1 * v u * pow2 64  +
      v f2 * v u * pow2 64 * pow2 64 +
      v f3 * v u * pow2 64 * pow2 64 * pow2 64 -
      v h3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 -
      v c2 * pow2 64 * pow2 64 * pow2 64 * pow2 64))
    (ensures as_nat4 out + (v h3 + v c2) * pow2 256 == as_nat4 f * v u)
let lemma_mul1_simplify out f u h3 c2 =
  lemma_mul_felem_u64 f u;
  lemma_mul_assos_5 (v h3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  lemma_mul_assos_5 (v c2) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert (as_nat4 out == as_nat4 f * v u - v h3 * pow2 256 - v c2 * pow2 256);
  assert (as_nat4 out + v h3 * pow2 256 + v c2 * pow2 256 == as_nat4 f * v u);
  FStar.Math.Lemmas.distributivity_add_left (v h3) (v c2) (pow2 256)

val lemma_mul1_add_no_carry:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 256}
  -> c:nat{c < pow2 256}
  -> d:nat{d < pow2 64}
  -> e:nat
  -> Lemma
    (requires
      b + c * d < pow2 320 /\
      a + e * pow2 256 == b + c * d)
    (ensures e < pow2 64)
let lemma_mul1_add_no_carry a b c d e =
  assert_norm (pow2 320 > 0);
  assert (a + e * pow2 256 < pow2 320);
  assert_norm (pow2 64 * pow2 256 = pow2 320)

val lemma_mul1_add:
    out:felem4 -> f3:felem4 -> out0:felem4
  -> c0:uint64 -> c1:uint64 -> c2:uint64 -> c3:uint64
  -> Lemma
    (requires (let (o0, o1, o2, o3) = out0 in
      let (f30, f31, f32, f33) = f3 in
      as_nat4 out ==
      v f30 + v o0 - v c0 * pow2 64 +
      (v f31 + v o1 + v c0 - v c1 * pow2 64) * pow2 64 +
      (v f32 + v o2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 +
      (v f33 + v o3 + v c2 - v c3 * pow2 64) * pow2 64 * pow2 64 * pow2 64))
    (ensures
      as_nat4 out == as_nat4 f3 + as_nat4 out0 -
      v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64)
let lemma_mul1_add out f3 out0 c0 c1 c2 c3 =
  let (o0, o1, o2, o3) = out0 in
  let (f30, f31, f32, f33) = f3 in
  assert (as_nat4 out ==
    v f30 + v o0 - v c0 * pow2 64 +
    (v f31 + v o1 + v c0 - v c1 * pow2 64) * pow2 64 +
    (v f32 + v o2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 +
    (v f33 + v o3 + v c2 - v c3 * pow2 64) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out ==
    v f30 + v o0 - v c0 * pow2 64 +
    v f31 * pow2 64 + v o1 * pow2 64 + v c0 * pow2 64 - v c1 * pow2 64 * pow2 64 +
    v f32 * pow2 64 * pow2 64 + v o2 * pow2 64 * pow2 64 + v c1 * pow2 64 * pow2 64 -
      v c2 * pow2 64 * pow2 64 * pow2 64 +
    v f33 * pow2 64 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64 +
      v c2 * pow2 64 * pow2 64 * pow2 64 - v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out == as_nat4 f3 + as_nat4 out0 -
      v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64)

val lemma_carry_wide:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 263}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 7)
let lemma_carry_wide a b c =
  assert_norm (pow2 263 > 0);
  assert (a + c * pow2 256 < pow2 263);
  assert_norm (pow2 7 * pow2 256 = pow2 263)

val lemma_feval_wide:
  f:felem_wide4
  -> Lemma (let (f0, f1, f2, f3, f4, f5, f6, f7) = f in
     (feval_wide f == (as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38) % prime))
let lemma_feval_wide f = admit()

val lemma_fsub4:
    out:felem4 -> f1:felem4 -> f2:felem4
  -> c0:uint64 -> c1:uint64
  -> Lemma
    (requires
      feval out == (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
      v c0 * 38 + v c1 * pow2 256 - v c1 * 38) % prime)
    (ensures feval out == fsub (feval f1) (feval f2))
let lemma_fsub4 out f1 f2 c0 c1 =
  assert (feval out == (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 + v c1 * pow2 256 - v c1 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 - v c1 * 38) (v c1 * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c1) (pow2 256) prime;
  lemma_prime ();
  assert ((v c1 * pow2 256) % prime == (v c1 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 - v c1 * 38) (v c1 * 38) prime;
  assert (feval out == (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 - v c0 * 38) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 - v c0 * 38) (v c0 * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c0) (pow2 256) prime;
  lemma_prime ();
  assert ((v c0 * pow2 256) % prime == (v c0 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 - v c0 * 38) (v c0 * 38) prime;
  assert (feval out == (as_nat4 f1 - as_nat4 f2) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (as_nat4 f1) (- as_nat4 f2) prime;
  lemma_mod_sub_distr ((as_nat4 f1) % prime) (as_nat4 f2) prime

val lemma_mul4_no_carry0:
    a:nat{a < pow2 64}
  -> b:nat{b < pow2 384}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 64 == b)
    (ensures c < pow2 320)
let lemma_mul4_no_carry0 a b c =
  assert (a + c * pow2 64 < pow2 384);
  assert_norm (pow2 320 * pow2 64 = pow2 384)

val lemma_mul4_no_carry1:
    a:nat{a < pow2 128}
  -> b:nat{b < pow2 448}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 64 * pow2 64 == b)
    (ensures c < pow2 320)
let lemma_mul4_no_carry1 a b c =
  assert (a + c * pow2 64 * pow2 64 < pow2 448);
  assert_norm (pow2 320 * pow2 64 * pow2 64 = pow2 448)

val lemma_fmul14:
  a:nat{a < pow2 256} -> b:nat{b < pow2 17}
  -> Lemma (a * b < pow2 273)
let lemma_fmul14 a b =
  assert_norm (pow2 256 * pow2 17 = pow2 273)

val lemma_fmul14_no_carry0:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 273}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 17)
let lemma_fmul14_no_carry0 a b c =
  assert (a + c * pow2 256 < pow2 273);
  assert_norm (pow2 17 * pow2 256 = pow2 273)
