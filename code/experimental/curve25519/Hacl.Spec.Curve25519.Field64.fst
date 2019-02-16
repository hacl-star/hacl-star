module Hacl.Spec.Curve25519.Field64

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes
open Spec.Curve25519
open Hacl.Helpers

open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.Curve25519.Field64.Lemmas
module SC = Hacl.Spec.Curve25519.Field64.Core

#reset-options "--z3rlimit 100  --using_facts_from '* -FStar.Seq'"

val lemma_prime19: unit ->
  Lemma (pow2 255 % prime == 19)
let lemma_prime19 () =
  assert_norm (pow2 255 % prime = 19 % prime);
  assert_norm (19 < prime);
  FStar.Math.Lemmas.modulo_lemma 19 prime

val lemma_add_le: a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma
  (requires (a <= b /\ c <= d))
  (ensures (a + c <= b + d))
let lemma_add_le a b c d = ()

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
  assert (as_nat4 f <= pow2 256 - 1);
  assert (as_nat4 f < 3 * prime);
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
  assert (as_nat4 f' <= pow2 64 - 1 + pow2 64 * pow2 64 - pow2 64 +
    pow2 64 * pow2 64 * pow2 64 - pow2 64 * pow2 64 + pow2 63 * pow2 64 * pow2 64 * pow2 64 -
    pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f' <= pow2 255 - 1);
  assert (19 * v top_bit <= 19);
  lemma_add_le (as_nat4 f') (pow2 255 - 1) (19 * v top_bit) 19;
  assert (as_nat4 f' + 19 * v top_bit <= pow2 255 + 18);
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
  assert (as_nat4 f' <= pow2 64 - 1 + pow2 64 * pow2 64 - pow2 64 +
    pow2 64 * pow2 64 * pow2 64 - pow2 64 * pow2 64 + pow2 63 * pow2 64 * pow2 64 * pow2 64 -
    pow2 64 * pow2 64 * pow2 64);
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

val lemma_subtract_p4_0:
    f:felem4
  -> f':felem4
  -> Lemma
    (requires (
      let (f0, f1, f2, f3) = f in
      let (f0', f1', f2', f3') = f' in
      v f3 < pow2 63 /\
      (v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3)))
    (ensures as_nat4 f' == as_nat4 f % prime)
let lemma_subtract_p4_0 f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  assert_norm (0xffffffffffffffed = pow2 64 - 19);
  assert (as_nat4 f == v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 - 20 + (pow2 64 - 1) * pow2 64 + (pow2 64 - 1) * pow2 64 * pow2 64 +
    (pow2 63 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (as_nat4 f < pow2 255 - 19);
  assert (as_nat4 f == as_nat4 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat4 f') prime

val lemma_subtract_p4_1:
    f:felem4
  -> f':felem4
  -> Lemma
    (requires
      (let (f0, f1, f2, f3) = f in
      let (f0', f1', f2', f3') = f' in
      (v f3 = 0x7fffffffffffffff && v f2 = 0xffffffffffffffff && v f1 = 0xffffffffffffffff && v f0 >= 0xffffffffffffffed) /\
      (v f0' = v f0 - 0xffffffffffffffed && v f1' = v f1 - 0xffffffffffffffff && v f2' = v f2 - 0xffffffffffffffff &&
       v f3' = v f3 - 0x7fffffffffffffff)))
    (ensures as_nat4 f' == as_nat4 f % prime)
let lemma_subtract_p4_1 f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  assert_norm (0xffffffffffffffed = pow2 64 - 19);
  assert (as_nat4 f' % prime ==
    (v f0' + v f1' * pow2 64 + v f2' * pow2 64 * pow2 64 + v f3' * pow2 64 * pow2 64 * pow2 64) % prime);
  assert (as_nat4 f' % prime ==
    (v f0 - (pow2 64 - 19) + (v f1 - (pow2 64 - 1)) * pow2 64 + (v f2 - (pow2 64 - 1)) * pow2 64 * pow2 64 +
    (v f3 - (pow2 63 - 1)) * pow2 64 * pow2 64 * pow2 64) % prime);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (as_nat4 f' % prime ==
    (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    v f3 * pow2 64 * pow2 64 * pow2 64 - prime) % prime);
  FStar.Math.Lemmas.lemma_mod_sub
    (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64) 1 prime

val lemma_subtract_p:
    f:felem4
  -> f':felem4
  -> Lemma
    (requires (
      let (f0, f1, f2, f3) = f in
      let (f0', f1', f2', f3') = f' in
      v f3 < pow2 63 /\
     (((v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3)) \/
     ((v f3 = 0x7fffffffffffffff && v f2 = 0xffffffffffffffff && v f1 = 0xffffffffffffffff && v f0 >= 0xffffffffffffffed) /\
      (v f0' = v f0 - 0xffffffffffffffed && v f1' = v f1 - 0xffffffffffffffff && v f2' = v f2 - 0xffffffffffffffff &&
       v f3' = v f3 - 0x7fffffffffffffff)))))
    (ensures as_nat4 f' == as_nat4 f % prime)
let lemma_subtract_p f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  if ((v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) &&
       (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3))
  then lemma_subtract_p4_0 f f'
  else lemma_subtract_p4_1 f f'

inline_for_extraction
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

  let mask0 = uint64_eq_mask f3 (u64 0x7fffffffffffffff) in
  let mask1 = mask0 &. uint64_eq_mask f2 (u64 0xffffffffffffffff) in
  let mask2 = mask1 &. uint64_eq_mask f1 (u64 0xffffffffffffffff) in
  let mask = mask2 &. uint64_gte_mask f0 (u64 0xffffffffffffffed) in

  let p0 = mask &. u64 0xffffffffffffffed in
  let p1 = mask &. u64 0xffffffffffffffff in
  let p2 = mask &. u64 0xffffffffffffffff in
  let p3 = mask &. u64 0x7fffffffffffffff in

  let f0' = f0 -. p0 in
  let f1' = f1 -. p1 in
  let f2' = f2 -. p2 in
  let f3' = f3 -. p3 in

  lemma_subtract_p (f0, f1, f2, f3) (f0', f1', f2', f3');
  (f0', f1', f2', f3')
