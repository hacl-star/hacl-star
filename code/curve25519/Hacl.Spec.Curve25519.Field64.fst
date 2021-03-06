module Hacl.Spec.Curve25519.Field64

open FStar.Mul

open Lib.Sequence
open Lib.IntTypes

open Spec.Curve25519
open Hacl.Spec.Curve25519.Field64.Definition

module Lemmas = Hacl.Spec.Curve25519.Field64.Lemmas
module CC = Hacl.Spec.Curve25519.Field64.Core

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum
module SL = Hacl.Spec.Bignum.Lib


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val carry_pass_store: f:CC.felem -> CC.felem
let carry_pass_store f =
  let top_bit = f.[3] >>. 63ul in
  let f3' = f.[3] &. u64 0x7fffffffffffffff in
  let r0 = f.[3] <- f3' in
  let (c, r1) = CC.add1 r0 (u64 19 *! top_bit) in
  r1


val lemma_carry_pass_store0: f:CC.felem ->
  Lemma (let out = carry_pass_store f in
    let top_bit = f.[3] >>. 63ul in
    SD.bn_v out == SD.bn_v f - prime * v top_bit /\
    SD.bn_v out % prime == SD.bn_v f % prime)
    //SD.bn_v out <= pow2 255 + 18)

let lemma_carry_pass_store0 f =
  let top_bit = f.[3] >>. 63ul in
  let f3' = f.[3] &. u64 0x7fffffffffffffff in
  Lemmas.lemma_carry_pass_store_f3 f;

  let r0 = f.[3] <- f3' in
  SD.bn_upd_eval f f3' 3;
  assert (SD.bn_v r0 == SD.bn_v f - v f.[3] * pow2 (3 * 64) + v f3' * pow2 (3 * 64));
  calc (==) {
    SD.bn_v f - v f.[3] * pow2 (3 * 64) + v f3' * pow2 (3 * 64);
    (==) { }
    SD.bn_v f - (v top_bit * pow2 63 + v f3') * pow2 (3 * 64) + v f3' * pow2 (3 * 64);
    (==) { Math.Lemmas.distributivity_add_left (v top_bit * pow2 63) (v f3') (pow2 (3 * 64)) }
    SD.bn_v f - (v top_bit * pow2 63) * pow2 (3 * 64);
    (==) { Math.Lemmas.paren_mul_right (v top_bit) (pow2 63) (pow2 (3 * 64)); Math.Lemmas.pow2_plus 63 (3 * 64) }
    SD.bn_v f - v top_bit * pow2 255;
    };

  assert (SD.bn_v r0 + v top_bit * pow2 255 == SD.bn_v f);
  let (c, r1) = CC.add1 r0 (u64 19 *! top_bit) in
  assert (SD.bn_v r1 + v c * pow2 256 == SD.bn_v r0 + 19 * v top_bit);
  SD.bn_eval_bound f 4;
  Lemmas.carry_pass_store_bound (SD.bn_v f) (v top_bit) (SD.bn_v r0) (SD.bn_v r1) (v c);

  calc (==) { //SD.bn_v r1 % prime ==
    (SD.bn_v r0 + 19 * v top_bit) % prime;
    (==) { }
    (SD.bn_v f - v top_bit * pow2 255 + 19 * v top_bit) % prime;
    (==) { Lemmas.lemma_mul_pow255_add (SD.bn_v f - v top_bit * pow2 255) (v top_bit) }
    (SD.bn_v f - v top_bit * pow2 255 + v top_bit * pow2 255) % prime;
    (==) { }
    SD.bn_v f % prime;
    }


val lemma_carry_pass_store_first: f:CC.felem -> Lemma
 (let out = carry_pass_store f in
  SD.bn_v out % prime == SD.bn_v f % prime /\
  SD.bn_v out < prime + 38)

let lemma_carry_pass_store_first f =
  let out = carry_pass_store f in
  let top_bit = f.[3] >>. 63ul in
  lemma_carry_pass_store0 f;
  assert (SD.bn_v out == SD.bn_v f - prime * v top_bit);
  Lemmas.lemma_carry_pass_store_f3 f


val lemma_carry_pass_store_second: f:CC.felem -> Lemma
  (requires SD.bn_v f < prime + 38)
  (ensures (let out = carry_pass_store f in
    SD.bn_v out % prime == SD.bn_v f % prime /\
    SD.bn_v out < pow2 255 /\ v out.[3] < pow2 63))

let lemma_carry_pass_store_second f =
  let out = carry_pass_store f in
  let top_bit = f.[3] >>. 63ul in
  lemma_carry_pass_store0 f;
  assert (SD.bn_v out == SD.bn_v f - prime * v top_bit);
  Lemmas.lemma_carry_pass_store_f3 f;
  if v top_bit = 0 then
    SD.bn_eval_inj 4 f out
  else begin
    assert (SD.bn_v out < 38);
    assert_norm (38 < pow2 7);
    SD.bn_eval_split_i out 3;
    SD.bn_eval1 (slice out 3 4);
    assert (SD.bn_v out == SD.bn_v (slice out 0 3) + v out.[3] * pow2 (64 * 3));
    SD.bn_eval_bound (slice out 0 3) 3;
    Math.Lemmas.pow2_lt_compat (64 * 3) 7;
    assert (v out.[3] = 0);
    () end


//lemma_carry_pass_store_second + subtract_p4 = bn_reduce_once
inline_for_extraction noextract
val subtract_p4: f:felem4 -> Pure felem4
  (requires (let (f0, f1, f2, f3) = f in
    v f3 < pow2 63 /\ as_nat4 f < pow2 255))
  (ensures fun out ->
    as_nat4 out == feval4 f /\ as_nat4 out < prime)

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
  Lemmas.lemma_subtract_p (f0, f1, f2, f3) (f0', f1', f2', f3');
  (f0', f1', f2', f3')
