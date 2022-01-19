module Hacl.Spec.K256.Field52.Lemmas4

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"


val lemma_as_nat_horner (r0 r1 r2 r3 r4:nat) :
  Lemma (r0 + r1 * pow52 + r2 * pow104 + r3 * pow156 + r4 * pow208 ==
    (((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0)

let lemma_as_nat_horner r0 r1 r2 r3 r4 =
  calc (==) {
    (((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r4 * pow2 52) r3 (pow2 52) }
    ((r4 * pow2 52 * pow2 52 + r3 * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r4 (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    ((r4 * pow2 104 + r3 * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r4 * pow2 104) (r3 * pow2 52 + r2) (pow2 52) }
    (r4 * pow2 104 * pow2 52 + (r3 * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r4 (pow2 104) (pow2 52); Math.Lemmas.pow2_plus 104 52 }
    (r4 * pow2 156 + (r3 * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r3 * pow2 52) r2 (pow2 52) }
    (r4 * pow2 156 + r3 * pow2 52 * pow2 52 + r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r3 (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    (r4 * pow2 156 + r3 * pow2 104 + r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r4 * pow2 156) (r3 * pow2 104 + r2 * pow2 52 + r1) (pow2 52) }
    r4 * pow2 156 * pow2 52 + (r3 * pow2 104 + r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r4 (pow2 156) (pow2 52); Math.Lemmas.pow2_plus 156 52 }
    r4 * pow2 208 + (r3 * pow2 104 + r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r3 * pow2 104) (r2 * pow2 52 + r1) (pow2 52) }
    r4 * pow2 208 + r3 * pow2 104 * pow2 52 + (r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r3 (pow2 104) (pow2 52); Math.Lemmas.pow2_plus 104 52 }
    r4 * pow2 208 + r3 * pow2 156 + (r2 * pow2 52 + r1) * pow2 52 + r0;
    (==) { Math.Lemmas.distributivity_add_left (r2 * pow2 52) r1 (pow2 52) }
    r4 * pow2 208 + r3 * pow2 156 + r2 * pow2 52 * pow2 52 + r1 * pow2 52 + r0;
    (==) { Math.Lemmas.paren_mul_right r2 (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    r4 * pow2 208 + r3 * pow2 156 + r2 * pow2 104 + r1 * pow2 52 + r0;
  }


val lemma_nat_r43 (r3 r4 c11 d4:nat) : Lemma
  (requires r3 = c11 % pow2 52 /\ r4 = c11 / pow2 52 + (d4 % pow2 52) % pow2 48)
  (ensures  r4 * pow2 52 + r3 = c11 + (d4 % pow2 48) * pow2 52)

let lemma_nat_r43 r3 r4 c11 d4 =
  Math.Lemmas.pow2_modulo_modulo_lemma_1 d4 48 52;
  Math.Lemmas.distributivity_add_left (c11 / pow2 52) (d4 % pow2 48) (pow2 52);
  Math.Lemmas.euclidean_division_definition c11 (pow2 52)


val lemma_nat_r432 (r2 r3 r4 c9 c11 d4 d11 t3 r:nat) : Lemma
  (requires
    r2 = c9 % pow2 52 /\ c11 = c9 / pow2 52 + r * pow2 12 * d11 + t3 /\
    r3 = c11 % pow2 52 /\ r4 = c11 / pow2 52 + (d4 % pow2 52) % pow2 48)
  (ensures
    (r4 * pow2 52 + r3) * pow2 52 + r2 =
    c9 + r * d11 * pow2 64 + t3 * pow2 52 + (d4 % pow2 48) * pow2 104)

let lemma_nat_r432 r2 r3 r4 c9 c11 d4 d11 t3 r =
  let k = d4 % pow2 48 in
  calc (==) {
    (r4 * pow2 52 + r3) * pow2 52 + r2;
    (==) { lemma_nat_r43 r3 r4 c11 d4 }
    (c11 + k * pow2 52) * pow2 52 + r2;
    (==) { Math.Lemmas.distributivity_add_left c11 (k * pow2 52) (pow2 52) }
    c11 * pow2 52 + k * pow2 52 * pow2 52 + r2;
    (==) { Math.Lemmas.paren_mul_right k (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    (c9 / pow2 52 + r * pow2 12 * d11 + t3) * pow2 52 + k * pow2 104 + c9 % pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (c9 / pow2 52) (r * pow2 12 * d11 + t3) (pow2 52) }
    c9 / pow2 52 * pow2 52 + (r * pow2 12 * d11 + t3) * pow2 52 + k * pow2 104 + c9 % pow2 52;
    (==) { Math.Lemmas.euclidean_division_definition c9 (pow2 52) }
    c9 + (r * pow2 12 * d11 + t3) * pow2 52 + k * pow2 104;
    (==) { Math.Lemmas.distributivity_add_left (r * pow2 12 * d11) t3 (pow2 52) }
    c9 + r * pow2 12 * d11 * pow2 52 + t3 * pow2 52 + k * pow2 104;
    (==) { Math.Lemmas.paren_mul_right r (pow2 12) d11; Math.Lemmas.swap_mul (pow2 12) d11 }
    c9 + r * (d11 * pow2 12) * pow2 52 + t3 * pow2 52 + k * pow2 104;
    (==) {
      Math.Lemmas.paren_mul_right r (d11 * pow2 12) (pow2 52);
      Math.Lemmas.paren_mul_right d11 (pow2 12) (pow2 52);
      Math.Lemmas.pow2_plus 12 52 }
    c9 + r * (d11 * pow2 64) + t3 * pow2 52 + k * pow2 104;
    (==) { Math.Lemmas.paren_mul_right r d11 (pow2 64) }
    c9 + r * d11 * pow2 64 + t3 * pow2 52 + k * pow2 104;
  }


val lemma_nat_r4321 (r1 r2 r3 r4 c6 c9 c11 d4 d10 d11 t3 r sum2:nat) : Lemma
  (requires
    d11 = d10 / pow2 64 /\
    r1 = c6 % pow2 52 /\ c9 = c6 / pow2 52 + sum2 + r * (d10 % pow2 64) /\
    r2 = c9 % pow2 52 /\ c11 = c9 / pow2 52 + r * pow2 12 * d11 + t3 /\
    r3 = c11 % pow2 52 /\ r4 = c11 / pow2 52 + (d4 % pow2 52) % pow2 48)
  (ensures
    ((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1 =
    c6 + sum2 * pow2 52 + r * d10 * pow2 52 + t3 * pow2 104 + (d4 % pow2 48) * pow2 156)

let lemma_nat_r4321 r1 r2 r3 r4 c6 c9 c11 d4 d10 d11 t3 r sum2 =
  let k = d4 % pow2 48 in
  let tmp1 = t3 * pow2 52 + k * pow2 104 in
  let tmp = r * d11 * pow2 64 + tmp1 in

  calc (==) {
    ((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1;
    (==) { lemma_nat_r432 r2 r3 r4 c9 c11 d4 d11 t3 r }
    (c9 + tmp) * pow2 52 + r1;
    (==) { Math.Lemmas.distributivity_add_left c9 tmp (pow2 52) }
    (c6 / pow2 52 + sum2 + r * (d10 % pow2 64)) * pow2 52 + tmp * pow2 52 + c6 % pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (c6 / pow2 52) (sum2 + r * (d10 % pow2 64)) (pow2 52) }
    c6 / pow2 52 * pow2 52 + (sum2 + r * (d10 % pow2 64)) * pow2 52 + tmp * pow2 52 + c6 % pow2 52;
    (==) { Math.Lemmas.euclidean_division_definition c6 (pow2 52) }
    c6 + (sum2 + r * (d10 % pow2 64)) * pow2 52 + tmp * pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (sum2 + r * (d10 % pow2 64)) tmp (pow2 52) }
    c6 + (sum2 + r * (d10 % pow2 64) + r * d11 * pow2 64 + tmp1) * pow2 52;
    (==) {
      Math.Lemmas.paren_mul_right r d11 (pow2 64);
      Math.Lemmas.distributivity_add_right r (d10 % pow2 64) (d11 * pow2 64);
      Math.Lemmas.euclidean_division_definition d10 (pow2 64) }
    c6 + (sum2 + r * d10 + t3 * pow2 52 + k * pow2 104) * pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (sum2 + r * d10 + t3 * pow2 52) (k * pow2 104) (pow2 52) }
    c6 + (sum2 + r * d10 + t3 * pow2 52) * pow2 52 + k * pow2 104 * pow2 52;
    (==) { Math.Lemmas.paren_mul_right k (pow2 104) (pow2 52); Math.Lemmas.pow2_plus 104 52 }
    c6 + (sum2 + r * d10 + t3 * pow2 52) * pow2 52 + k * pow2 156;
    (==) { Math.Lemmas.distributivity_add_left (sum2 + r * d10) (t3 * pow2 52) (pow2 52) }
    c6 + (sum2 + r * d10) * pow2 52 + t3 * pow2 52 * pow2 52 + k * pow2 156;
    (==) { Math.Lemmas.paren_mul_right t3 (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    c6 + (sum2 + r * d10) * pow2 52 + t3 * pow2 104 + k * pow2 156;
    (==) { Math.Lemmas.distributivity_add_left sum2 (r * d10) (pow2 52) }
    c6 + sum2 * pow2 52 + r * d10 * pow2 52 + t3 * pow2 104 + k * pow2 156;
    }


val lemma_nat_r43210 (r0 r1 r2 r3 r4 c3 c6 c9 c11 d4 d8 d10 d11 t3 r sum1 sum2 sum7:nat) : Lemma
  (requires
    d10 == d8 / pow2 52 + sum7 /\
    r0 = c3 % pow2 52 /\ c6 = c3 / pow2 52 + sum1 + d8 % pow2 52 * r /\
    d11 = d10 / pow2 64 /\
    r1 = c6 % pow2 52 /\ c9 = c6 / pow2 52 + sum2 + r * (d10 % pow2 64) /\
    r2 = c9 % pow2 52 /\ c11 = c9 / pow2 52 + r * pow2 12 * d11 + t3 /\
    r3 = c11 % pow2 52 /\ r4 = c11 / pow2 52 + (d4 % pow2 52) % pow2 48)
  (ensures
    r0 + r1 * pow52 + r2 * pow104 + r3 * pow156 + r4 * pow208 =
    c3 + (sum1 + r * d8) * pow2 52 + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + (d4 % pow2 48) * pow2 208)

let lemma_nat_r43210 r0 r1 r2 r3 r4 c3 c6 c9 c11 d4 d8 d10 d11 t3 r sum1 sum2 sum7 =
  let k = d4 % pow2 48 in
  let tmp1 = sum2 * pow2 52 + t3 * pow2 104 + k * pow2 156 in
  let tmp = r * d10 * pow2 52 + tmp1 in

  calc (==) {
    r0 + r1 * pow52 + r2 * pow104 + r3 * pow156 + r4 * pow208;
    (==) { lemma_as_nat_horner r0 r1 r2 r3 r4 }
    (((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { lemma_nat_r4321 r1 r2 r3 r4 c6 c9 c11 d4 d10 d11 t3 r sum2 }
    (c3 / pow2 52 + sum1 + d8 % pow2 52 * r + tmp) * pow2 52 + c3 % pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (c3 / pow2 52) (sum1 + d8 % pow2 52 * r + tmp) (pow2 52) }
    c3 / pow2 52 * pow2 52 + (sum1 + d8 % pow2 52 * r + tmp) * pow2 52 + c3 % pow2 52;
    (==) { Math.Lemmas.euclidean_division_definition c3 (pow2 52) }
    c3 + (sum1 + d8 % pow2 52 * r + r * d10 * pow2 52 + tmp1) * pow2 52;
    (==) {
      Math.Lemmas.swap_mul (d8 % pow2 52) r;
      Math.Lemmas.paren_mul_right r d10 (pow2 52);
      Math.Lemmas.distributivity_add_right r (d8 % pow2 52) (d10 * pow2 52) }
    c3 + (sum1 + r * (d8 % pow2 52 + (d8 / pow2 52 + sum7) * pow2 52) + tmp1) * pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (d8 / pow2 52) sum7 (pow2 52) }
    c3 + (sum1 + r * (d8 % pow2 52 + d8 / pow2 52 * pow2 52 + sum7 * pow2 52) + tmp1) * pow2 52;
    (==) { Math.Lemmas.euclidean_division_definition d8 (pow2 52) }
    c3 + (sum1 + r * (d8 + sum7 * pow2 52) + tmp1) * pow2 52;
    (==) {
      Math.Lemmas.distributivity_add_right r d8 (sum7 * pow2 52);
      Math.Lemmas.paren_mul_right r sum7 (pow2 52) }
    c3 + (sum1 + r * d8 + r * sum7 * pow2 52 + tmp1) * pow2 52;
    (==) { Math.Lemmas.distributivity_add_left (sum1 + r * d8 + tmp1) (r * sum7 * pow2 52) (pow2 52) }
    c3 + (sum1 + r * d8 + tmp1) * pow2 52 + r * sum7 * pow2 52 * pow2 52;
    (==) {
      Math.Lemmas.paren_mul_right r sum7 (pow2 52);
      Math.Lemmas.paren_mul_right r (sum7 * pow2 52) (pow2 52);
      Math.Lemmas.paren_mul_right sum7 (pow2 52) (pow2 52) }
    c3 + (sum1 + r * d8 + tmp1) * pow2 52 + r * (sum7 * (pow2 52 * pow2 52));
    (==) { Math.Lemmas.pow2_plus 52 52; Math.Lemmas.paren_mul_right r sum7 (pow2 104) }
    c3 + (sum1 + r * d8 + tmp1) * pow2 52 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.distributivity_add_left (sum1 + r * d8) tmp1 (pow2 52) }
    c3 + (sum1 + r * d8) * pow2 52 + (sum2 * pow2 52 + t3 * pow2 104 + k * pow2 156) * pow2 52 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.distributivity_add_left (sum2 * pow2 52 + t3 * pow2 104) (k * pow2 156) (pow2 52) }
    c3 + (sum1 + r * d8) * pow2 52 + (sum2 * pow2 52 + t3 * pow2 104) * pow2 52 + k * pow2 156 * pow2 52 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.paren_mul_right k (pow2 156) (pow2 52); Math.Lemmas.pow2_plus 156 52 }
    c3 + (sum1 + r * d8) * pow2 52 + (sum2 * pow2 52 + t3 * pow2 104) * pow2 52 + k * pow2 208 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.paren_mul_right (sum2 * pow2 52) (t3 * pow2 104) (pow2 52) }
    c3 + (sum1 + r * d8) * pow2 52 + sum2 * pow2 52 * pow2 52 + t3 * pow2 104 * pow2 52 + k * pow2 208 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.paren_mul_right sum2 (pow2 52) (pow2 52); Math.Lemmas.pow2_plus 52 52 }
    c3 + (sum1 + r * d8) * pow2 52 + sum2 * pow2 104 + t3 * pow2 104 * pow2 52 + k * pow2 208 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.paren_mul_right t3 (pow2 104) (pow2 52); Math.Lemmas.pow2_plus 104 52 }
    c3 + (sum1 + r * d8) * pow2 52 + sum2 * pow2 104 + t3 * pow2 156 + k * pow2 208 + r * sum7 * pow2 104;
    (==) { Math.Lemmas.distributivity_add_left sum2 (r * sum7) (pow2 104) }
    c3 + (sum1 + r * d8) * pow2 52 + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + k * pow2 208;
    }


val simplify_c3 (d4 r sum5:nat) : Lemma
  (requires r % pow2 4 = 0)
  (ensures
    ((d4 % pow2 52) / pow2 48 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4) ==
    (d4 / pow2 48) * (r / pow2 4) + ((d4 / pow2 52 + sum5) % pow2 52 - (d4 / pow2 52)) * r)

let simplify_c3 d4 r sum5 =
  calc (==) { //simplify c3
    ((d4 % pow2 52) / pow2 48 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4);
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 d4 48 52 }
    ((d4 / pow2 48) % pow2 4 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4);
    (==) { Math.Lemmas.euclidean_division_definition (d4 / pow2 48) (pow2 4) }
    (d4 / pow2 48 - (d4 / pow2 48 / pow2 4) * pow2 4 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4);
    (==) { Math.Lemmas.division_multiplication_lemma d4 (pow2 48) (pow2 4); Math.Lemmas.pow2_plus 48 4 }
    (d4 / pow2 48 - (d4 / pow2 52) * pow2 4 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4);
    (==) { Math.Lemmas.distributivity_sub_left ((d4 / pow2 52 + sum5) % pow2 52) (d4 / pow2 52) (pow2 4) }
    (d4 / pow2 48 + ((d4 / pow2 52 + sum5) % pow2 52 - d4 / pow2 52) * pow2 4) * (r / pow2 4);
    (==) { Math.Lemmas.distributivity_add_left (d4 / pow2 48) (((d4 / pow2 52 + sum5) % pow2 52 - d4 / pow2 52) * pow2 4) (r / pow2 4) }
    (d4 / pow2 48) * (r / pow2 4) + ((d4 / pow2 52 + sum5) % pow2 52 - d4 / pow2 52) * pow2 4 * (r / pow2 4);
    (==) { Math.Lemmas.paren_mul_right ((d4 / pow2 52 + sum5) % pow2 52 - d4 / pow2 52) (pow2 4) (r / pow2 4); Math.Lemmas.div_exact_r r (pow2 4) }
    (d4 / pow2 48) * (r / pow2 4) + ((d4 / pow2 52 + sum5) % pow2 52 - d4 / pow2 52) * r;
  }


val lemma_nat_r43210_mod_prime (c3 d4 d8 t3 r sum0 sum1 sum2 sum3 sum4 sum5 sum6 sum7 sum8: nat) : Lemma
  (requires
    r  = 0x1000003D10 /\
    d4 = (sum3 + r * (sum8 % pow2 64)) / pow2 52 + sum4 + r * pow2 12 * (sum8 / pow2 64) /\
    t3 = (sum3 + r * (sum8 % pow2 64)) % pow2 52 /\
    d8 = (d4 / pow2 52 + sum5) / pow2 52 + sum6 /\
    c3 = sum0 + ((d4 % pow2 52) / pow2 48 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4))
  (ensures
    (c3 + (sum1 + r * d8) * pow2 52 + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + (d4 % pow2 48) * pow2 208) % S.prime ==
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104 + (sum3 + r * sum8) * pow2 156 + sum4 * pow2 208) % S.prime)

let lemma_nat_r43210_mod_prime c3 d4 d8 t3 r sum0 sum1 sum2 sum3 sum4 sum5 sum6 sum7 sum8 =
  let tmp2 = sum3 + r * (sum8 % pow2 64) in
  let tmp1 = d4 / pow2 52 + sum5 in
  let tmp0 = sum0 + (tmp1 % pow2 52 - d4 / pow2 52) * r in

  calc (==) {
    (c3 + (sum1 + r * d8) * pow2 52 + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + (d4 % pow2 48) * pow2 208) % S.prime;
    (==) { simplify_c3 d4 r sum5; assert_norm (0x1000003D10 / pow2 4 = 0x1000003D1) }
    (tmp0 + (sum1 + r * d8) * pow2 52 +
      (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + (d4 % pow2 48) * pow2 208 + (d4 / pow2 48) * 0x1000003D1) % S.prime;
    (==) { LD.as_nat_mod_prime tmp0 (sum1 + r * d8) (sum2 + r * sum7) t3 d4 }
    (tmp0 + (sum1 + r * d8) * pow2 52 + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + d4 * pow2 208) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left sum1 (r * (tmp1 / pow2 52 + sum6)) (pow2 52) }
    (sum0 + (tmp1 % pow2 52 - d4 / pow2 52) * r + sum1 * pow2 52 + r * (tmp1 / pow2 52 + sum6) * pow2 52
      + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + d4 * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right r (tmp1 / pow2 52 + sum6) (pow2 52);
      Math.Lemmas.swap_mul r ((tmp1 / pow2 52 + sum6) * pow2 52);
      Math.Lemmas.paren_mul_right (tmp1 / pow2 52 + sum6) (pow2 52) r }
    (sum0 + (tmp1 % pow2 52 - d4 / pow2 52) * r + sum1 * pow2 52 + (tmp1 / pow2 52 + sum6) * (pow2 52 * r)
      + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + d4 * pow2 208) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left (tmp1 / pow2 52) sum6 (pow2 52 * r) }
    (sum0 + (tmp1 % pow2 52 - d4 / pow2 52) * r + sum1 * pow2 52 + tmp1 / pow2 52 * (pow2 52 * r) + sum6 * (pow2 52 * r)
      + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + d4 * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right (tmp1 / pow2 52) (pow2 52) r;
      Math.Lemmas.distributivity_add_left (tmp1 % pow2 52 - (d4 / pow2 52)) (tmp1 / pow2 52 * pow2 52) r;
      Math.Lemmas.euclidean_division_definition tmp1 (pow2 52) }
    (sum0 + sum5 * r + sum1 * pow2 52 + sum6 * (pow2 52 * r)
      + (sum2 + r * sum7) * pow2 104 + t3 * pow2 156 + d4 * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.swap_mul (pow2 52) r;
      Math.Lemmas.paren_mul_right sum6 r (pow2 52);
      Math.Lemmas.distributivity_add_left sum1 (sum6 * r) (pow2 52) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (tmp2 % pow2 52) * pow2 156 + (tmp2 / pow2 52 + sum4 + r * pow2 12 * (sum8 / pow2 64)) * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.distributivity_add_left (tmp2 / pow2 52) (sum4 + r * pow2 12 * (sum8 / pow2 64)) (pow2 208);
      Math.Lemmas.pow2_plus 52 156;
      Math.Lemmas.paren_mul_right (tmp2 / pow2 52) (pow2 52) (pow2 156) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (tmp2 % pow2 52) * pow2 156 + tmp2 / pow2 52 * pow2 52 * pow2 156
      + (sum4 + r * pow2 12 * (sum8 / pow2 64)) * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.distributivity_add_left (tmp2 % pow2 52) (tmp2 / pow2 52 * pow2 52) (pow2 156);
      Math.Lemmas.euclidean_division_definition tmp2 (pow2 52) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * (sum8 % pow2 64)) * pow2 156 + (sum4 + r * pow2 12 * (sum8 / pow2 64)) * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right r (pow2 12) (sum8 / pow2 64);
      Math.Lemmas.swap_mul (pow2 12) (sum8 / pow2 64);
      Math.Lemmas.paren_mul_right r (sum8 / pow2 64) (pow2 12) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * (sum8 % pow2 64)) * pow2 156 + (sum4 + r * (sum8 / pow2 64) * pow2 12) * pow2 208) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left sum4 (r * (sum8 / pow2 64) * pow2 12) (pow2 208) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * (sum8 % pow2 64)) * pow2 156 + sum4 * pow2 208 + r * (sum8 / pow2 64) * pow2 12 * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right (r * (sum8 / pow2 64)) (pow2 12) (pow2 208);
      Math.Lemmas.pow2_plus 12 208; Math.Lemmas.pow2_plus 64 156;
      Math.Lemmas.paren_mul_right (r * (sum8 / pow2 64)) (pow2 64) (pow2 156) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * (sum8 % pow2 64)) * pow2 156 + sum4 * pow2 208 + r * (sum8 / pow2 64) * pow2 64 * pow2 156) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left (sum3 + r * (sum8 % pow2 64)) (r * (sum8 / pow2 64) * pow2 64) (pow2 156) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * (sum8 % pow2 64) + r * (sum8 / pow2 64) * pow2 64) * pow2 156 + sum4 * pow2 208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right r (sum8 / pow2 64) (pow2 64);
      Math.Lemmas.distributivity_add_right r (sum8 % pow2 64) ((sum8 / pow2 64) * pow2 64);
      Math.Lemmas.euclidean_division_definition sum8 (pow2 64) }
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
      + (sum3 + r * sum8) * pow2 156 + sum4 * pow2 208) % S.prime;
    }


val lemma_distr5 (a0 a1 a2 a3 a4 b: nat) : Lemma
  ((a0 + a1 + a2 + a3 + a4) * b = a0 * b + a1 * b + a2 * b + a3 * b + a4 * b)

let lemma_distr5 a0 a1 a2 a3 a4 b =
  calc (==) {
    (a0 + a1 + a2 + a3 + a4) * b;
    (==) { Math.Lemmas.distributivity_add_left a0 (a1 + a2 + a3 + a4) b }
    a0 * b + (a1 + a2 + a3 + a4) * b;
    (==) { Math.Lemmas.distributivity_add_left a1 (a2 + a3 + a4) b }
    a0 * b + a1 * b + (a2 + a3 + a4) * b;
    (==) { Math.Lemmas.distributivity_add_left a2 (a3 + a4) b }
    a0 * b + a1 * b + a2 * b + (a3 + a4) * b;
    (==) { Math.Lemmas.distributivity_add_left a3 a3 b }
    a0 * b + a1 * b + a2 * b + a3 * b + a4 * b;
    }


val lemma_distr5_pow52 (a b0 b1 b2 b3 b4: nat) : Lemma
  (a * (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) =
   a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156 + a * b4 * pow2 208)

let lemma_distr5_pow52 a b0 b1 b2 b3 b4 =
  let b_sum = b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208 in
  calc (==) {
    a * b_sum;
    (==) { Math.Lemmas.swap_mul a b_sum; lemma_distr5 b0 (b1 * pow52) (b2 * pow104) (b3 * pow156) (b4 * pow208) a }
    b0 * a + b1 * pow2 52 * a + b2 * pow2 104 * a + b3 * pow2 156 * a + b4 * pow2 208 * a;
    (==) {
      Math.Lemmas.swap_mul (b1 * pow2 52) a; Math.Lemmas.paren_mul_right a b1 (pow2 52);
      Math.Lemmas.swap_mul (b2 * pow2 104) a; Math.Lemmas.paren_mul_right a b2 (pow2 104);
      Math.Lemmas.swap_mul (b3 * pow2 156) a; Math.Lemmas.paren_mul_right a b3 (pow2 156);
      Math.Lemmas.swap_mul (b4 * pow2 208) a; Math.Lemmas.paren_mul_right a b4 (pow2 208) }
    a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156 + a * b4 * pow2 208;
  }


val lemma_distr5_pow52_mul_pow (a b0 b1 b2 b3 b4 p: nat) : Lemma
  (a * pow2 p * (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) =
   a * b0 * pow2 p + a * b1 * pow2 (52 + p) + a * b2 * pow2 (104 + p) + a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p))

let lemma_distr5_pow52_mul_pow a b0 b1 b2 b3 b4 p =
  let b_sum = b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208 in
  calc (==) {
    a * pow2 p * b_sum;
    (==) {
      Math.Lemmas.paren_mul_right a (pow2 p) b_sum;
      Math.Lemmas.swap_mul (pow2 p) b_sum;
      Math.Lemmas.paren_mul_right a b_sum (pow2 p) }
    a * b_sum * pow2 p;
    (==) { lemma_distr5_pow52 a b0 b1 b2 b3 b4 }
    (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156 + a * b4 * pow2 208) * pow2 p;
    (==) { lemma_distr5 (a * b0) (a * b1 * pow2 52) (a * b2 * pow2 104) (a * b3 * pow2 156) (a * b4 * pow2 208) (pow2 p) }
    a * b0 * pow2 p + a * b1 * pow2 52 * pow2 p + a * b2 * pow2 104 * pow2 p + a * b3 * pow2 156 * pow2 p + a * b4 * pow2 208 * pow2 p;
    (==) {
      Math.Lemmas.paren_mul_right (a * b1) (pow2 52) (pow2 p); Math.Lemmas.pow2_plus 52 p;
      Math.Lemmas.paren_mul_right (a * b2) (pow2 104) (pow2 p); Math.Lemmas.pow2_plus 104 p;
      Math.Lemmas.paren_mul_right (a * b3) (pow2 156) (pow2 p); Math.Lemmas.pow2_plus 156 p;
      Math.Lemmas.paren_mul_right (a * b4) (pow2 208) (pow2 p); Math.Lemmas.pow2_plus 208 p }
    a * b0 * pow2 p + a * b1 * pow2 (52 + p) + a * b2 * pow2 (104 + p) + a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p);
    }


val lemma_mul_ab (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4:nat) :
  Lemma
   (let sum0 = a0 * b0 in
    let sum1 = a0 * b1 + a1 * b0 in
    let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
    let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
    let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
    let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
    let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
    let sum7 = a3 * b4 + a4 * b3 in
    let sum8 = a4 * b4 in
    (a0 + a1 * pow52 + a2 * pow104 + a3 * pow156 + a4 * pow208) *
    (b0 + b1 * pow52 + b2 * pow104 + b3 * pow156 + b4 * pow208) =
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208 +
    pow2 260 * (sum5 + sum6 * pow2 52 + sum7 * pow2 104 + sum8 * pow2 156))

let lemma_mul_ab a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  let sum0 = a0 * b0 in
  let sum1 = a0 * b1 + a1 * b0 in
  let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
  let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
  let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
  let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
  let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
  let sum7 = a3 * b4 + a4 * b3 in
  let sum8 = a4 * b4 in

  let b_sum = b0 + b1 * pow52 + b2 * pow104 + b3 * pow156 + b4 * pow208 in
  calc (==) {
    (a0 + a1 * pow52 + a2 * pow104 + a3 * pow156 + a4 * pow208) * b_sum;
    (==) { lemma_distr5 a0 (a1 * pow52) (a2 * pow104) (a3 * pow156) (a4 * pow208) b_sum }
    a0 * b_sum + a1 * pow52 * b_sum + a2 * pow104 * b_sum + a3 * pow156 * b_sum + a4 * pow208 * b_sum;
    (==) { lemma_distr5_pow52 a0 b0 b1 b2 b3 b4 }
    sum0 + a0 * b1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * pow52 * b_sum + a2 * pow104 * b_sum + a3 * pow156 * b_sum + a4 * pow208 * b_sum;
    (==) { lemma_distr5_pow52_mul_pow a1 b0 b1 b2 b3 b4 52 }
    sum0 + a0 * b1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b0 * pow2 52 + a1 * b1 * pow2 104 + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * pow104 * b_sum + a3 * pow156 * b_sum + a4 * pow208 * b_sum;
    (==) { lemma_distr5_pow52_mul_pow a2 b0 b1 b2 b3 b4 104 }
    sum0 + a0 * b1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b0 * pow2 52 + a1 * b1 * pow2 104 + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b0 * pow2 104 + a2 * b1 * pow2 156 + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * pow156 * b_sum + a4 * pow208 * b_sum;
    (==) { lemma_distr5_pow52_mul_pow a3 b0 b1 b2 b3 b4 156 }
    sum0 + a0 * b1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b0 * pow2 52 + a1 * b1 * pow2 104 + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b0 * pow2 104 + a2 * b1 * pow2 156 + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b0 * pow2 156 + a3 * b1 * pow2 208 + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * pow208 * b_sum;
    (==) { lemma_distr5_pow52_mul_pow a4 b0 b1 b2 b3 b4 208 }
    sum0 + a0 * b1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b0 * pow2 52 + a1 * b1 * pow2 104 + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b0 * pow2 104 + a2 * b1 * pow2 156 + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b0 * pow2 156 + a3 * b1 * pow2 208 + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b0 * pow2 208 + a4 * b1 * pow2 260 + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { Math.Lemmas.distributivity_add_left (a0 * b1) (a1 * b0) (pow2 52) }
    sum0 + sum1 * pow2 52 + a0 * b2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b1 * pow2 104 + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b0 * pow2 104 + a2 * b1 * pow2 156 + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b0 * pow2 156 + a3 * b1 * pow2 208 + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b0 * pow2 208 + a4 * b1 * pow2 260 + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { lemma_distr5 (a0 * b2) (a1 * b1) (a2 * b0) 0 0 (pow2 104) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + a0 * b3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b2 * pow2 156 + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b1 * pow2 156 + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b0 * pow2 156 + a3 * b1 * pow2 208 + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b0 * pow2 208 + a4 * b1 * pow2 260 + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { lemma_distr5 (a0 * b3) (a1 * b2) (a2 * b1) (a3 * b0) 0 (pow2 156) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + a0 * b4 * pow2 208
    + a1 * b3 * pow2 208 + a1 * b4 * pow2 260
    + a2 * b2 * pow2 208 + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b1 * pow2 208 + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b0 * pow2 208 + a4 * b1 * pow2 260 + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { lemma_distr5 (a0 * b4) (a1 * b3) (a2 * b2) (a3 * b1) (a4 * b0) (pow2 208) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + a1 * b4 * pow2 260
    + a2 * b3 * pow2 260 + a2 * b4 * pow2 312
    + a3 * b2 * pow2 260 + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b1 * pow2 260 + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { lemma_distr5 (a1 * b4) (a2 * b3) (a3 * b2) (a4 * b1) 0 (pow2 260) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + sum5 * pow2 260
    + a2 * b4 * pow2 312
    + a3 * b3 * pow2 312 + a3 * b4 * pow2 364
    + a4 * b2 * pow2 312 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { lemma_distr5 (a2 * b4) (a3 * b3) (a4 * b2) 0 0 (pow2 312) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + sum5 * pow2 260 + sum6 * pow2 312 + a3 * b4 * pow2 364 + a4 * b3 * pow2 364 + a4 * b4 * pow2 416;
    (==) { Math.Lemmas.distributivity_add_left (a3 * b4) (a4 * b3) (pow2 364) }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + sum5 * pow2 260 + sum6 * pow2 312 + sum7 * pow2 364 + sum8 * pow2 416;
    (==) { lemma_distr5_pow52_mul_pow 1 sum5 sum6 sum7 sum8 0 260 }
    sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + pow2 260 * (sum5 + sum6 * pow2 52 + sum7 * pow2 104 + sum8 * pow2 156);
    }


val lemma_fmul_ab (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4:nat) :
  Lemma
   (let sum0 = a0 * b0 in
    let sum1 = a0 * b1 + a1 * b0 in
    let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
    let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
    let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
    let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
    let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
    let sum7 = a3 * b4 + a4 * b3 in
    let sum8 = a4 * b4 in
    let r = 0x1000003D10 in
    (a0 + a1 * pow52 + a2 * pow104 + a3 * pow156 + a4 * pow208) *
    (b0 + b1 * pow52 + b2 * pow104 + b3 * pow156 + b4 * pow208) % S.prime =
    (sum0 + sum5 * r + (sum1 + sum6 * r) * pow2 52 + (sum2 + r * sum7) * pow2 104
    + (sum3 + r * sum8) * pow2 156 + sum4 * pow2 208) % S.prime)

let lemma_fmul_ab a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  let r = 0x1000003D10 in
  let sum0 = a0 * b0 in
  let sum1 = a0 * b1 + a1 * b0 in
  let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
  let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
  let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
  let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
  let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
  let sum7 = a3 * b4 + a4 * b3 in
  let sum8 = a4 * b4 in
  let a_sum = a0 + a1 * pow52 + a2 * pow104 + a3 * pow156 + a4 * pow208 in
  let b_sum = b0 + b1 * pow52 + b2 * pow104 + b3 * pow156 + b4 * pow208 in

  let tmp0 = sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208 in
  let tmp1 = sum5 + sum6 * pow2 52 + sum7 * pow2 104 + sum8 * pow2 156 in

  calc (==) {
    a_sum * b_sum % S.prime;
    (==) { lemma_mul_ab a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 }
    (tmp0 + pow2 260 * tmp1) % S.prime;
    (==) { Math.Lemmas.pow2_plus 256 4; Math.Lemmas.paren_mul_right (pow2 256) (pow2 4) tmp1 }
    (tmp0 + pow2 256 * (pow2 4 * tmp1)) % S.prime;
    (==) { LD.lemma_a_plus_b_mul_pow256 tmp0 (pow2 4 * tmp1) }
    (tmp0 + 0x1000003D1 * (pow2 4 * tmp1)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right 0x1000003D1 (pow2 4) tmp1; assert_norm (0x1000003D1 * pow2 4 = r) }
    (tmp0 + r * tmp1) % S.prime;
    (==) { lemma_distr5_pow52 r sum5 sum6 sum7 sum8 0 }
    (sum0 + sum1 * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + r * sum5 + r * sum6 * pow2 52 + r * sum7 * pow2 104 + r * sum8 * pow2 156) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left sum1 (r * sum6) (pow2 52) }
    (sum0 + r * sum5 + (sum1 + r * sum6) * pow2 52 + sum2 * pow2 104 + sum3 * pow2 156 + sum4 * pow2 208
    + r * sum7 * pow2 104 + r * sum8 * pow2 156) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left sum2 (r * sum7) (pow2 104) }
    (sum0 + r * sum5 + (sum1 + r * sum6) * pow2 52 + (sum2 + r * sum7) * pow2 104
    + sum3 * pow2 156 + sum4 * pow2 208 + r * sum8 * pow2 156) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left sum3 (r * sum8) (pow2 156) }
    (sum0 + r * sum5 + (sum1 + r * sum6) * pow2 52 + (sum2 + r * sum7) * pow2 104
    + (sum3 + r * sum8) * pow2 156 + sum4 * pow2 208) % S.prime;
    }


val lemma_fmul_simplify
  (r0 r1 r2 r3 r4 c3 c6 c9 c11 d4 d8 d10 d11 t3
   a0 a1 a2 a3 a4 b0 b1 b2 b3 b4:nat) : Lemma
  (requires (
    let r = 0x1000003D10 in
    let sum0 = a0 * b0 in
    let sum1 = a0 * b1 + a1 * b0 in
    let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
    let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
    let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
    let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
    let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
    let sum7 = a3 * b4 + a4 * b3 in
    let sum8 = a4 * b4 in
    d4 = (sum3 + r * (sum8 % pow2 64)) / pow2 52 + sum4 + r * pow2 12 * (sum8 / pow2 64) /\
    t3 = (sum3 + r * (sum8 % pow2 64)) % pow2 52 /\
    d8 = (d4 / pow2 52 + sum5) / pow2 52 + sum6 /\
    c3 = sum0 + ((d4 % pow2 52) / pow2 48 + ((d4 / pow2 52 + sum5) % pow2 52) * pow2 4) * (r / pow2 4) /\
    d10 = d8 / pow2 52 + sum7 /\
    r0 = c3 % pow2 52 /\ c6 = c3 / pow2 52 + sum1 + d8 % pow2 52 * r /\
    d11 = d10 / pow2 64 /\
    r1 = c6 % pow2 52 /\ c9 = c6 / pow2 52 + sum2 + r * (d10 % pow2 64) /\
    r2 = c9 % pow2 52 /\ c11 = c9 / pow2 52 + r * pow2 12 * d11 + t3 /\
    r3 = c11 % pow2 52 /\ r4 = c11 / pow2 52 + (d4 % pow2 52) % pow2 48))
  (ensures
    (r0 + r1 * pow52 + r2 * pow104 + r3 * pow156 + r4 * pow208) % S.prime =
    (a0 + a1 * pow52 + a2 * pow104 + a3 * pow156 + a4 * pow208) *
    (b0 + b1 * pow52 + b2 * pow104 + b3 * pow156 + b4 * pow208) % S.prime)

let lemma_fmul_simplify r0 r1 r2 r3 r4 c3 c6 c9 c11 d4 d8 d10 d11 t3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  let r = 0x1000003D10 in
  let sum0 = a0 * b0 in
  let sum1 = a0 * b1 + a1 * b0 in
  let sum2 = a0 * b2 + a1 * b1 + a2 * b0 in
  let sum3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 in
  let sum4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 in
  let sum5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 in
  let sum6 = a2 * b4 + a3 * b3 + a4 * b2 in
  let sum7 = a3 * b4 + a4 * b3 in
  let sum8 = a4 * b4 in

  lemma_nat_r43210 r0 r1 r2 r3 r4 c3 c6 c9 c11 d4 d8 d10 d11 t3 r sum1 sum2 sum7;
  lemma_nat_r43210_mod_prime c3 d4 d8 t3 r sum0 sum1 sum2 sum3 sum4 sum5 sum6 sum7 sum8;
  lemma_fmul_ab a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
