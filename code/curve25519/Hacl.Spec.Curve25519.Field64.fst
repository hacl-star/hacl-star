module Hacl.Spec.Curve25519.Field64

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes
open Spec.Curve25519

open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.Curve25519.Field64.Lemmas
module SC = Hacl.Spec.Curve25519.Field64.Core

#reset-options "--z3rlimit 200  --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val carry_pass_store:
  f:felem4
 -> felem4
let carry_pass_store (f0, f1, f2, f3) =
  let top_bit = f3 >>. 63ul in
  let f3' = f3 &. u64 0x7fffffffffffffff in
  let f' = (f0, f1, f2, f3') in
  let c, r = SC.add1 f' (u64 19 *! top_bit) in
  r

val lemma_carry_pass_store0: f:felem4 ->
  Lemma
   (let out = carry_pass_store f in
    feval out == feval f /\ as_nat4 out <= pow2 255 + 18)
let lemma_carry_pass_store0 f =
  let (f0, f1, f2, f3) = f in
  lemma_as_nat4 f;
  let top_bit = f3 >>. 63ul in
  let f3' = f3 &. u64 0x7fffffffffffffff in
  mod_mask_lemma f3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  uintv_extensionality (mod_mask #U64 63ul) (u64 0x7fffffffffffffff);
  FStar.Math.Lemmas.euclidean_division_definition (v f3) (pow2 63);
  assert (v f3 == v top_bit * pow2 63 + v f3');
  assert (v top_bit <= 1);
  assert (feval f == (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    (v top_bit * pow2 63 + v f3') * pow2 64 * pow2 64 * pow2 64) % prime);
  assert (feval f == (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    v top_bit * pow2 63 * pow2 64 * pow2 64 * pow2 64 + v f3' * pow2 64 * pow2 64 * pow2 64) % prime);
  let f' = (f0, f1, f2, f3') in
  assert (feval f == (as_nat4 f' + v top_bit * pow2 63 * pow2 64 * pow2 64 * pow2 64) % prime);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (feval f == (as_nat4 f' + v top_bit * pow2 255) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f') (v top_bit * pow2 255) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v top_bit) (pow2 255) prime;
  lemma_prime19 ();
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f') (v top_bit * 19) prime;
  assert (feval f == (as_nat4 f' + v top_bit * 19) % prime);
  let c, r = SC.add1 f' (u64 19 *! top_bit) in
  assert (as_nat4 r + v c * pow2 256 == as_nat4 f' + 19 * v top_bit);
  assert (as_nat4 f' <= (pow2 64 - 1) + (pow2 64 - 1) * pow2 64 +
    (pow2 64 - 1) * pow2 64 * pow2 64 + (pow2 63 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f' <= pow2 255 - 1);
  assert (19 * v top_bit <= 19);
  lemma_add_le (as_nat4 f') (pow2 255 - 1) (19 * v top_bit) 19;
  assert (as_nat4 r + v c * pow2 256 <= pow2 255 + 18)

val lemma_carry_pass_store1_0: f:felem4 ->
  Lemma
   (requires (
     let (f0, f1, f2, f3) = f in
     as_nat4 f <= pow2 255 + 18 /\ v f3 < pow2 63))
    (ensures (
      let out = carry_pass_store f in
      let (o0, o1, o2, o3) = out in
      feval out == feval f /\
      as_nat4 out < pow2 255 /\
      v o3 < pow2 63))
let lemma_carry_pass_store1_0 f =
  let (f0, f1, f2, f3) = f in
  let top_bit = f3 >>. 63ul in
  let f3' = f3 &. u64 0x7fffffffffffffff in
  mod_mask_lemma f3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  uintv_extensionality (mod_mask #U64 63ul) (u64 0x7fffffffffffffff);
  FStar.Math.Lemmas.euclidean_division_definition (v f3) (pow2 63);
  assert (v top_bit = 0);
  assert (v f3 == v f3');
  let f' = (f0, f1, f2, f3') in
  let c, r = SC.add1 f' (u64 19 *! top_bit) in
  assert (as_nat4 r == as_nat4 f');
  assert (as_nat4 f' <= (pow2 64 - 1) + (pow2 64 - 1) * pow2 64 +
    (pow2 64 - 1) * pow2 64 * pow2 64 + (pow2 63 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f' <= pow2 255 - 1)

val lemma_carry_pass_store1_1: f:felem4 ->
  Lemma
   (requires (
     let (f0, f1, f2, f3) = f in
     as_nat4 f <= pow2 255 + 18 /\ v f3 >= pow2 63))
    (ensures (
      let out = carry_pass_store f in
      let (o0, o1, o2, o3) = out in
      feval out == feval f /\
      as_nat4 out < pow2 255 /\
      v o3 < pow2 63))
let lemma_carry_pass_store1_1 f =
  let (f0, f1, f2, f3) = f in
  assert (pow2 63 * pow2 64 * pow2 64 * pow2 64 <= as_nat4 f);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (pow2 255 <= as_nat4 f);
  assert (v f1 == 0);
  assert (v f2 == 0);
  assert (v f0 < 19);
  let top_bit = f3 >>. 63ul in
  let f3' = f3 &. u64 0x7fffffffffffffff in
  mod_mask_lemma f3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  uintv_extensionality (mod_mask #U64 63ul) (u64 0x7fffffffffffffff);
  FStar.Math.Lemmas.euclidean_division_definition (v f3) (pow2 63);
  assert (v f3 == pow2 63 + v f3');

  assert (feval f == (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    (pow2 63 + v f3') * pow2 64 * pow2 64 * pow2 64) % prime);
  assert (feval f == (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    pow2 63 * pow2 64 * pow2 64 * pow2 64 + v f3' * pow2 64 * pow2 64 * pow2 64) % prime);
  let f' = (f0, f1, f2, f3') in
  assert (feval f == (as_nat4 f' + pow2 63 * pow2 64 * pow2 64 * pow2 64) % prime);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (feval f == (as_nat4 f' + pow2 255) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f') (v top_bit * pow2 255) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v top_bit) (pow2 255) prime;
  lemma_prime19 ();
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f') (v top_bit * 19) prime;
  assert (feval f == (as_nat4 f' + 19) % prime);
  let c, r = SC.add1 f' (u64 19) in
  assert (as_nat4 r + v c * pow2 256 == as_nat4 f' + 19);
  assert (as_nat4 f' == v f0 + v f3' * pow2 64 * pow2 64 * pow2 64);
  assert (v f3' <= 1);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert (as_nat4 f' + 19 < prime);
  assert (as_nat4 r < prime)

val lemma_carry_pass_store1: f:felem4 ->
  Lemma
    (requires as_nat4 f <= pow2 255 + 18)
    (ensures (
      let out = carry_pass_store f in
      let (o0, o1, o2, o3) = out in
      feval out == feval f /\
      as_nat4 out < pow2 255 /\
      v o3 < pow2 63))
let lemma_carry_pass_store1 f =
  let (f0, f1, f2, f3) = f in
  if (v f3 < pow2 63) then
    lemma_carry_pass_store1_0 f
  else
    lemma_carry_pass_store1_1 f

inline_for_extraction noextract
val subtract_p4:
    f:felem4
  -> Pure felem4
    (requires (let (f0, f1, f2, f3) = f in
      v f3 < pow2 63 /\ as_nat4 f < pow2 255))
    (ensures fun out ->
      as_nat4 out == feval f /\ as_nat4 out < prime)
let subtract_p4 (f0, f1, f2, f3) =
  // assert_norm (0x8000000000000000 = pow2 63);
  // assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  // assert_norm (0xffffffffffffffff = pow2 64 - 1);
  // assert_norm (0xffffffffffffffed = pow2 64 - 19);

  let m0 = gte_mask f0 (u64 0xffffffffffffffed) in
  let m1 = eq_mask f1 (u64 0xffffffffffffffff) in
  let m2 = eq_mask f2 (u64 0xffffffffffffffff) in
  let m3 = eq_mask f3 (u64 0x7fffffffffffffff) in
  let mask = m0 &. m1 &. m2 &. m3 in
  let f0' = f0 -. (mask &. u64 0xffffffffffffffed) in
  let f1' = f1 -. (mask &. u64 0xffffffffffffffff) in
  let f2' = f2 -. (mask &. u64 0xffffffffffffffff) in
  let f3' = f3 -. (mask &. u64 0x7fffffffffffffff) in
  logand_lemma mask (u64 0xffffffffffffffed);
  logand_lemma mask (u64 0x7fffffffffffffff);
  logand_lemma mask (u64 0xffffffffffffffff);
  lemma_subtract_p (f0, f1, f2, f3) (f0', f1', f2', f3');
  (f0', f1', f2', f3')
