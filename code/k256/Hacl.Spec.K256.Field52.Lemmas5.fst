module Hacl.Spec.K256.Field52.Lemmas5

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module ML = Hacl.Spec.K256.MathLemmas
module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

val lemma_bound_mul64_wide (ma mb:nat) (mma mmb:nat) (a b:uint64) : Lemma
  (requires v a <= ma * mma /\ v b <= mb * mmb)
  (ensures  (let r = mul64_wide a b in
    v r = v a * v b /\ v r <= ma * mb * (mma * mmb)))

let lemma_bound_mul64_wide ma mb mma mmb a b =
  ML.lemma_bound_mul64_wide ma mb mma mmb (v a) (v b)


val lemma_four_mul64_wide (a0 a1 a2 a3 b0 b1 b2 b3:uint64) : Lemma
  (requires
    felem_fits1 a0 64 /\ felem_fits1 b0 64 /\
    felem_fits1 a1 64 /\ felem_fits1 b1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 b2 64 /\
    felem_fits1 a3 64 /\ felem_fits1 b3 64)
  (ensures
   (let d = mul64_wide a0 b3 +. mul64_wide a1 b2 +. mul64_wide a2 b1 +. mul64_wide a3 b0 in
    v d = v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0 /\
    v d <= 16384 * (max52 * max52)))

let lemma_four_mul64_wide a0 a1 a2 a3 b0 b1 b2 b3 =
  lemma_bound_mul64_wide 64 64 max52 max52 a0 b3;
  lemma_bound_mul64_wide 64 64 max52 max52 a1 b2;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 b1;
  lemma_bound_mul64_wide 64 64 max52 max52 a3 b0;
  assert (v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0 <= 16384 * (max52 * max52));
  assert_norm (16384 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v a0 * v b3 + v a1 * v b2) (pow2 128);
  Math.Lemmas.small_mod (v a0 * v b3 + v a1 * v b2 + v a2 * v b1) (pow2 128);
  Math.Lemmas.small_mod (v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0) (pow2 128)


val lemma_16_max52_max48: a:pos -> Lemma ((a * 16) * (max52 * max48) < a * (max52 * max52))
let lemma_16_max52_max48 a =
  assert_norm (16 * (max52 * max48) < max52 * max52);
  calc (<) {
    (a * 16) * (max52 * max48);
    (==) { Math.Lemmas.paren_mul_right a 16 (max52 * max48) }
    a * (16 * (max52 * max48));
    (<) { Math.Lemmas.lemma_mult_lt_left a (16 * (max52 * max48)) (max52 * max52) }
    a * (max52 * max52);
  }


val lemma_add_five_mul64_wide (md:nat) (d:uint128) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 16385 /\
    felem_fits1 a0 64 /\ felem_fits1 b0 64 /\
    felem_fits1 a1 64 /\ felem_fits1 b1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 b2 64 /\
    felem_fits1 a3 64 /\ felem_fits1 b3 64 /\
    felem_fits_last1 a4 64 /\ felem_fits_last1 b4 64)
  (ensures
   (let d1 = d +. mul64_wide a0 b4 +. mul64_wide a1 b3 +.
     mul64_wide a2 b2 +. mul64_wide a3 b1 +. mul64_wide a4 b0 in
    v d1 == v d + v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0 /\
    v d1 <= 12801 * (max52 * max52)))

let lemma_add_five_mul64_wide md d a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  lemma_bound_mul64_wide 64 64 max52 max48 a0 b4;
  lemma_bound_mul64_wide 64 64 max52 max52 a1 b3;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 b2;
  lemma_bound_mul64_wide 64 64 max52 max52 a3 b1;
  lemma_bound_mul64_wide 64 64 max48 max52 a4 b0;
  Math.Lemmas.swap_mul max52 max48;
  assert (v d + v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0 <=
    md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52);
    (<) { lemma_16_max52_max48 512 }
    md * max52 + 12800 * (max52 * max52);
    (<=) { assert_norm (16385 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 12800 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 12800 (max52 * max52) }
    12801 * (max52 * max52);
    };
  assert_norm (12801 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a0 * v b4) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b4 + v a1 * v b3) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b4 + v a1 * v b3 + v a2 * v b2) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0) (pow2 128)


val lemma_add_four_mul64_wide (md:nat) (d:uint128) (a1 a2 a3 a4 b1 b2 b3 b4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 12802 /\
    felem_fits1 a1 64 /\ felem_fits1 b1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 b2 64 /\
    felem_fits1 a3 64 /\ felem_fits1 b3 64 /\
    felem_fits_last1 a4 64 /\ felem_fits_last1 b4 64)
  (ensures
   (let d1 = d +. mul64_wide a1 b4 +. mul64_wide a2 b3 +.
     mul64_wide a3 b2 +. mul64_wide a4 b1 in
    v d1 == v d + v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1 /\
    v d1 <= 8705 * (max52 * max52)))

let lemma_add_four_mul64_wide md d a1 a2 a3 a4 b1 b2 b3 b4 =
  lemma_bound_mul64_wide 64 64 max52 max48 a1 b4;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 b3;
  lemma_bound_mul64_wide 64 64 max52 max52 a3 b2;
  lemma_bound_mul64_wide 64 64 max48 max52 a4 b1;
  assert (v d + v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1 <=
    md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52);
    (<) { lemma_16_max52_max48 512 }
    md * max52 + 8704 * (max52 * max52);
    (<=) { assert_norm (12802 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 8704 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 8704 (max52 * max52) }
    8705 * (max52 * max52);
    };
  assert_norm (8705 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a1 * v b4) (pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * v b4 + v a2 * v b3) (pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * v b4 + v a2 * v b3 + v a3 * v b2) (pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1) (pow2 128)


val lemma_add_three_mul64_wide52 (md:nat) (d:uint128) (a0 a1 a2 b0 b1 b2:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 8194 /\
    felem_fits1 a0 64 /\ felem_fits1 b0 64 /\
    felem_fits1 a1 64 /\ felem_fits1 b1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 b2 64)
  (ensures
   (let d1 = d +. mul64_wide a0 b2 +. mul64_wide a1 b1 +. mul64_wide a2 b0 in
    v d1 == v d + v a0 * v b2 + v a1 * v b1 + v a2 * v b0 /\
    v d1 <= 12289 * (max52 * max52)))

let lemma_add_three_mul64_wide52 md d a0 a1 a2 b0 b1 b2 =
  lemma_bound_mul64_wide 64 64 max52 max52 a0 b2;
  lemma_bound_mul64_wide 64 64 max52 max52 a1 b1;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 b0;
  assert (v d + v a0 * v b2 + v a1 * v b1 + v a2 * v b0 <=
    md * max52 + 12288 * (max52 * max52));

  calc (<=) {
    md * max52 + 12288 * (max52 * max52);
    (<=) { assert_norm (8194 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 12288 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 12288 (max52 * max52) }
    12289 * (max52 * max52);
    };
  assert_norm (12289 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a0 * v b2) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b2 + v a1 * v b1) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b2 + v a1 * v b1 + v a2 * v b0) (pow2 128)


val lemma_add_three_mul64_wide (md:nat) (d:uint128) (a2 a3 a4 b2 b3 b4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 8705 /\
    felem_fits1 a2 64 /\ felem_fits1 b2 64 /\
    felem_fits1 a3 64 /\ felem_fits1 b3 64 /\
    felem_fits_last1 a4 64 /\ felem_fits_last1 b4 64)
  (ensures
   (let d1 = d +. mul64_wide a2 b4 +. mul64_wide a3 b3 +. mul64_wide a4 b2 in
    v d1 == v d + v a2 * v b4 + v a3 * v b3 + v a4 * v b2 /\
    v d1 <= 4609 * (max52 * max52)))

let lemma_add_three_mul64_wide md d a2 a3 a4 b2 b3 b4 =
  lemma_bound_mul64_wide 64 64 max52 max48 a2 b4;
  lemma_bound_mul64_wide 64 64 max52 max52 a3 b3;
  lemma_bound_mul64_wide 64 64 max48 max52 a4 b2;
  Math.Lemmas.swap_mul max52 max48;
  assert (v d + v a2 * v b4 + v a3 * v b3 + v a4 * v b2 <=
    md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52);
    (<) { lemma_16_max52_max48 512 }
    md * max52 + 4608 * (max52 * max52);
    (<=) { assert_norm (8705 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 4608 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 4608 (max52 * max52) }
    4609 * (max52 * max52);
    };
  assert_norm (4609 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a2 * v b4) (pow2 128);
  Math.Lemmas.small_mod (v d + v a2 * v b4 + v a3 * v b3) (pow2 128);
  Math.Lemmas.small_mod (v d + v a2 * v b4 + v a3 * v b3 + v a4 * v b2) (pow2 128)


val lemma_add_two_mul64_wide52 (md:nat) (d:uint128) (a0 a1 b0 b1:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 4097 /\
    felem_fits1 a0 64 /\ felem_fits1 b0 64 /\
    felem_fits1 a1 64 /\ felem_fits1 b1 64)
  (ensures
   (let d1 = d +. mul64_wide a0 b1 +. mul64_wide a1 b0 in
    v d1 == v d + v a0 * v b1 + v a1 * v b0 /\
    v d1 <= 8193 * (max52 * max52)))

let lemma_add_two_mul64_wide52 md d a0 a1 b0 b1 =
  lemma_bound_mul64_wide 64 64 max52 max52 a0 b1;
  lemma_bound_mul64_wide 64 64 max52 max52 a1 b0;
  assert (v d + v a0 * v b1 + v a1 * v b0 <= md * max52 + 8192 * (max52 * max52));

  calc (<=) {
    md * max52 + 8192 * (max52 * max52);
    (<=) { assert_norm (4097 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 8192 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 8192 (max52 * max52) }
    8193 * (max52 * max52);
    };
  assert_norm (8193 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a0 * v b1) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * v b1 + v a1 * v b0) (pow2 128)


val lemma_add_two_mul64_wide (md:nat) (d:uint128) (a3 a4 b3 b4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 8193 /\
    felem_fits1 a3 64 /\ felem_fits1 b3 64 /\
    felem_fits_last1 a4 64 /\ felem_fits_last1 b4 64)
  (ensures
   (let d1 = d +. mul64_wide a3 b4 +. mul64_wide a4 b3 in
    v d1 == v d + v a3 * v b4 + v a4 * v b3 /\
    v d1 <= 513 * (max52 * max52)))

let lemma_add_two_mul64_wide md d a3 a4 b3 b4 =
  lemma_bound_mul64_wide 64 64 max52 max48 a3 b4;
  lemma_bound_mul64_wide 64 64 max48 max52 a4 b3;
  Math.Lemmas.swap_mul max52 max48;
  assert (v d + v a3 * v b4 + v a4 * v b3 <= md * max52 + 8192 * (max52 * max48));

  calc (<) {
    md * max52 + 8192 * (max52 * max48);
    (<) { lemma_16_max52_max48 512 }
    md * max52 + 512 * (max52 * max52);
    (<=) { assert_norm (8193 < max52); Math.Lemmas.lemma_mult_le_right max52 md max52 }
    max52 * max52 + 512 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left 1 512 (max52 * max52) }
    513 * (max52 * max52);
    };
  assert_norm (513 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a3 * v b4) (pow2 128);
  Math.Lemmas.small_mod (v d + v a3 * v b4 + v a4 * v b3) (pow2 128)


val lemma_r_lsh12: unit ->
  Lemma (let rs = u64 0x1000003D10 <<. 12ul in
    v rs = 0x1000003D10 * pow2 12 /\ v rs < pow2 49)

let lemma_r_lsh12 () =
  let rs = u64 0x1000003D10 <<. 12ul in
  assert_norm (0x1000003D10 < pow2 37);
  assert (v rs = 0x1000003D10 * pow2 12 % pow2 64);

  calc (<) {
    0x1000003D10 * pow2 12;
    (<) { Math.Lemmas.lemma_mult_lt_right (pow2 12) 0x1000003D10 (pow2 37) }
    pow2 37 * pow2 12;
    (==) { Math.Lemmas.pow2_plus 12 37 }
    pow2 49;
  };

  Math.Lemmas.pow2_lt_compat 64 49;
  Math.Lemmas.small_mod (0x1000003D10 * pow2 12) (pow2 64);
  assert (v rs = 0x1000003D10 * pow2 12)


val lemma_r_rsh4: unit ->
  Lemma (let rs = u64 0x1000003D10 >>. 4ul in
    v rs = 0x1000003D10 / pow2 4 /\ v rs < pow2 33)

let lemma_r_rsh4 () =
  let rs = u64 0x1000003D10 >>. 4ul in
  assert_norm (0x1000003D10 < pow2 37);
  Math.Lemmas.lemma_div_lt 0x1000003D10 37 4


val lemma_add_mul64_wide (pa pb md:nat) (d:uint128) (a b:uint64) : Lemma
  (requires
    v a < pow2 pa /\ v b < pow2 pb /\ md + 1 <= 16385 /\ // md + 1 <= pow2 24
    v d <= md * (max52 * max52) /\ pa + pb <= 103)
  (ensures (let r = d +. mul64_wide a b in
    v r = v d + v a * v b /\ v r <= (md + 1) * (max52 * max52)))

let lemma_add_mul64_wide pa pb md d a b =
  let r = d +. mul64_wide a b in
  lemma_bound_mul64_wide 1 1 (pow2 pa) (pow2 pb) a b;
  assert (v d + v a * v b <= md * (max52 * max52) + pow2 pa * pow2 pb);

  calc (<) {
    md * (max52 * max52) + pow2 pa * pow2 pb;
    (==) { Math.Lemmas.pow2_plus pa pb }
    md * (max52 * max52) + pow2 (pa + pb);
    (<=) { Math.Lemmas.pow2_le_compat 103 (pa + pb) }
    md * (max52 * max52) + pow2 103;
    (<) { assert_norm (pow2 103 < max52 * max52) }
    md * (max52 * max52) + max52 * max52;
    (==) { Math.Lemmas.distributivity_add_left md 1 (max52 * max52) }
    (md + 1) * (max52 * max52);
  };

  Math.Lemmas.lemma_mult_le_right (max52 * max52) (md + 1) 16385;
  assert_norm (16385 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a * v b) (pow2 128)


val lemma_bound_add_mul64_wide_r (md:nat) (d c:uint128) : Lemma
  (requires v d <= md * (max52 * max52) /\ md <= 16384)
  (ensures  (let r = d +. mul64_wide (u64 0x1000003D10) (to_u64 c) in
    v r = v d + 0x1000003D10 * (v c % pow2 64) /\ v r <= (md + 1) * (max52 * max52)))

let lemma_bound_add_mul64_wide_r md d c =
  assert_norm (0x1000003D10 < pow2 37);
  lemma_add_mul64_wide 37 64 md d (u64 0x1000003D10) (to_u64 c)


val lemma_bound_add_mul64_wide_r_lsh12 (md:nat) (d:uint128) (c:uint64) : Lemma
  (requires v d <= md * (max52 * max52) /\ md <= 12801 /\ v c <= pow2 44)
  (ensures  (let r = d +. mul64_wide (u64 0x1000003D10 <<. 12ul) c in
    v r = v d + 0x1000003D10 * pow2 12 * v c /\ v r <= (md + 1) * (max52 * max52)))

let lemma_bound_add_mul64_wide_r_lsh12 md d c =
  let rs = u64 0x1000003D10 <<. 12ul in
  lemma_r_lsh12 ();
  Math.Lemmas.pow2_lt_compat 45 44;
  lemma_add_mul64_wide 49 45 md d rs c


val lemma_bound_add_mul64_wide_r_rsh4 (md:nat) (d:uint128) (c:uint64) : Lemma
  (requires v d <= md * (max52 * max52) /\ md <= 4096 /\ v c < pow2 56)
  (ensures  (let r = d +. mul64_wide c (u64 0x1000003D10 >>. 4ul) in
    v r = v d + v c * (0x1000003D10 / pow2 4) /\ v r <= (md + 1) * (max52 * max52)))

let lemma_bound_add_mul64_wide_r_rsh4 md d c =
  let rs = u64 0x1000003D10 >>. 4ul in
  lemma_r_rsh4 ();
  lemma_add_mul64_wide 33 56 md d rs c


val lemma_bound_add_mul64_wide_r_lsh12_add (md:nat) (c:uint128) (d t3:uint64) : Lemma
  (requires v c <= md * max52 /\ md <= 12290 /\ v d < pow2 50 /\ felem_fits1 t3 1)
  (ensures  (let r = c +. mul64_wide (u64 0x1000003D10 <<. 12ul) d +. to_u128 t3 in
    v r = v c + 0x1000003D10 * pow2 12 * v d + v t3 /\ v r < pow2 100))

let lemma_bound_add_mul64_wide_r_lsh12_add md c d t3 =
  let rs = u64 0x1000003D10 <<. 12ul in
  lemma_r_lsh12 ();
  assert (v rs = 0x1000003D10 * pow2 12 /\ v rs < pow2 49);

  let r = c +. mul64_wide rs d +. to_u128 t3 in
  lemma_bound_mul64_wide 1 1 (pow2 49) (pow2 50) rs d;
  assert (v (mul64_wide rs d) = v rs * v d /\ v rs * v d < pow2 49 * pow2 50);

  calc (<) {
    md * max52 + pow2 49 * pow2 50 + max52;
    (==) { Math.Lemmas.pow2_plus 49 50 }
    md * max52 + pow2 99 + max52;
    (==) { Math.Lemmas.distributivity_add_left md 1 max52 }
    (md + 1) * max52 + pow2 99;
    (<=) { Math.Lemmas.lemma_mult_le_right max52 (md + 1) 12291 }
    12291 * max52 + pow2 99;
    (<) { assert_norm (12291 * max52 + pow2 99 < pow2 100) }
    pow2 100;
  };

  Math.Lemmas.pow2_lt_compat 128 100;
  Math.Lemmas.small_mod (v c + v rs * v d) (pow2 128);
  Math.Lemmas.small_mod (v c + v rs * v d + v t3) (pow2 128)


val lemma_u128_div52: md:pos -> a:uint128 -> Lemma
  (requires v a <= md * max52 * max52)
  (ensures  v a / pow2 52 <= md * max52)

let lemma_u128_div52 md a =
  Math.Lemmas.lemma_mult_lt_left (md * max52) max52 (pow2 52);
  Math.Lemmas.lemma_div_le (v a) (md * max52 * pow2 52) (pow2 52);
  Math.Lemmas.multiple_division_lemma (md * max52) (pow2 52)


val lemma_u128_div64_max48: md:pos -> a:uint128 -> Lemma
  (requires v a <= md * (max48 * max48))
  (ensures  v a / pow2 64 <= md * pow2 32)

let lemma_u128_div64_max48 md a =
  assert_norm (max48 < pow2 48);
  ML.lemma_ab_lt_cd max48 max48 (pow2 48) (pow2 48);
  Math.Lemmas.pow2_plus 48 48;
  assert (max48 * max48 < pow2 96);

  Math.Lemmas.lemma_mult_le_left md (max48 * max48) (pow2 96);
  assert (v a < md * pow2 96);
  Math.Lemmas.lemma_div_le (v a) (md * pow2 96) (pow2 64);
  Math.Lemmas.pow2_plus 64 32;
  Math.Lemmas.multiple_division_lemma (md * pow2 32) (pow2 64)


val lemma_u128_div64_max52: md:pos -> a:uint128 -> Lemma
  (requires v a <= md * (max52 * max52))
  (ensures  v a / pow2 64 <= md * pow2 40)

let lemma_u128_div64_max52 md a =
  assert_norm (max52 < pow2 52);
  ML.lemma_ab_lt_cd max52 max52 (pow2 52) (pow2 52);
  Math.Lemmas.pow2_plus 52 52;
  assert (max52 * max52 < pow2 104);

  Math.Lemmas.lemma_mult_le_left md (max52 * max52) (pow2 104);
  assert (v a < md * pow2 104);
  Math.Lemmas.lemma_div_le (v a) (md * pow2 104) (pow2 64);
  Math.Lemmas.pow2_plus 64 40;
  Math.Lemmas.multiple_division_lemma (md * pow2 40) (pow2 64)


val lemma_bound_c0: c0:uint128 -> Lemma
  (requires v c0 <= 4096 * (max48 * max48))
  (ensures  v c0 / pow2 64 <= pow2 44)

let lemma_bound_c0 c0 =
  lemma_u128_div64_max48 4096 c0;
  assert_norm (pow2 12 = 4096);
  Math.Lemmas.pow2_plus 12 32


val lemma_bound_d10: d10:uint128 -> Lemma
  (requires v d10 <= 513 * (max52 * max52))
  (ensures  v d10 / pow2 64 < pow2 50)

let lemma_bound_d10 d10 =
  lemma_u128_div64_max52 513 d10;
  assert_norm (513 < pow2 10);
  Math.Lemmas.lemma_mult_le_right (pow2 38) 513 (pow2 10);
  Math.Lemmas.pow2_plus 10 40


val lemma_bound_rsh64_to: a:uint128 ->
  Lemma (v (to_u64 (a >>. 64ul)) = v a / pow2 64)

let lemma_bound_rsh64_to a =
  let r = to_u64 (a >>. 64ul) in
  assert (v r == (v a / pow2 64) % pow2 64);
  Math.Lemmas.lemma_div_lt (v a) 128 64;
  Math.Lemmas.small_mod (v a / pow2 64) (pow2 64)


val lemma_u128_to_u64_mask52: d:uint128 ->
  Lemma (let r = to_u64 d &. mask52 in
    v r = v d % pow2 52 /\ felem_fits1 r 1)

let lemma_u128_to_u64_mask52 d =
  let r = to_u64 d &. mask52 in
  LD.lemma_mask52 (to_u64 d);
  assert (v r = v d % pow2 64 % pow2 52);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v d) 52 64


val lemma_bound_mask52_rsh52: md:pos -> d:uint128 -> Lemma
  (requires v d <= md * (max52 * max52) /\ md <= 16385)
  (ensures (let r = to_u64 d &. mask52 in let k = d >>. 52ul in
    v r = v d % pow2 52 /\ v k = v d / pow2 52 /\
    felem_fits1 r 1 /\ v k <= md * max52))

let lemma_bound_mask52_rsh52 md d =
  lemma_u128_to_u64_mask52 d;
  lemma_u128_div52 md d


val lemma_bound_add_mul64_wide_r_mask52 (md:pos) (d8 c5:uint128) : Lemma
  (requires v d8 <= md * (max52 * max52) /\ v c5 <= md * (max52 * max52) /\ md <= 8193)
  (ensures  (let r = c5 +. mul64_wide (to_u64 d8 &. mask52) (u64 0x1000003D10) in
    let d9 = d8 >>. 52ul in v d9 = v d8 / pow2 52 /\ v d9 <= md * max52 /\
    v r = v c5 + v d8 % pow2 52 * 0x1000003D10 /\ v r <= (md + 1) * (max52 * max52)))

let lemma_bound_add_mul64_wide_r_mask52 md d8 c5 =
  let tm = to_u64 d8 &. mask52 in
  lemma_bound_mask52_rsh52 md d8;
  assert_norm (0x1000003D10 < pow2 37);
  lemma_add_mul64_wide 64 37 md c5 tm (u64 0x1000003D10)


val lemma_bound_mask48_rsh48: t4:uint64 -> Lemma
  (requires felem_fits1 t4 1)
  (ensures (let tx = t4 >>. 48ul in let r = t4 &. mask48 in
    v tx = v t4 / pow2 48 /\ v r = v t4 % pow2 48 /\
    felem_fits_last1 r 1 /\ v tx < pow2 4))

let lemma_bound_mask48_rsh48 t4 =
  LD.lemma_mask48 t4;
  Math.Lemmas.lemma_div_lt (v t4) 52 48


val lemma_bound_mask52_rsh52_sp: d:uint128 -> Lemma
  (requires v d < pow2 100)
  (ensures (let r = to_u64 d &. mask52 in let k = to_u64 (d >>. 52ul) in
    v r = v d % pow2 52 /\ v k = v d / pow2 52 /\
    felem_fits1 r 1 /\ v k < pow2 48))

let lemma_bound_mask52_rsh52_sp d =
  let r = to_u64 d &. mask52 in
  lemma_u128_to_u64_mask52 d;

  let k = to_u64 (d >>. 52ul) in
  assert (v k == v d / pow2 52 % pow2 64);
  Math.Lemmas.lemma_div_lt (v d) 100 52;
  Math.Lemmas.pow2_lt_compat 64 48;
  Math.Lemmas.small_mod (v d / pow2 52) (pow2 64)


val lemma_tx_logor_u0_lsh4 (tx u0:uint64) : Lemma
  (requires v tx < pow2 4 /\ felem_fits1 u0 1)
  (ensures (let u0' = tx |. (u0 <<. 4ul) in
    v u0' == v tx + v u0 * pow2 4 /\ v u0' < pow2 56))

let lemma_tx_logor_u0_lsh4 tx u0 =
  let u0' = tx |. (u0 <<. 4ul) in
  assert (v (u0 <<. 4ul) = v u0 * pow2 4 % pow2 64);

  calc (<=) {
    v u0 * pow2 4;
    (<=) { Math.Lemmas.lemma_mult_le_right (pow2 4) (v u0) (pow2 52 - 1) }
    (pow2 52 - 1) * pow2 4;
    (==) { Math.Lemmas.distributivity_sub_left (pow2 52) 1 (pow2 4) }
    pow2 52 * pow2 4 - pow2 4;
    (==) { Math.Lemmas.pow2_plus 52 4 }
    pow2 56 - pow2 4;
    };

  assert (v u0 * pow2 4 <= pow2 56 - pow2 4);
  Math.Lemmas.pow2_lt_compat 64 56;
  Math.Lemmas.small_mod (v u0 * pow2 4) (pow2 64);
  assert (v (u0 <<. 4ul) = v u0 * pow2 4);

  Math.Lemmas.lemma_div_lt (v u0) 52 4;
  Math.Lemmas.cancel_mul_mod (v u0) (pow2 4);
  logor_disjoint tx (u0 <<. 4ul) 4;
  assert (v u0' == v tx + v u0 * pow2 4);
  assert (v u0' < pow2 56)


val lemma_mod_add_last (c12 t4':uint64) : Lemma
  (requires v c12 < pow2 48 /\ v t4' < pow2 48)
  (ensures (let r4 = c12 +. t4' in
    v r4 = v c12 + v t4' /\ felem_fits_last1 r4 2))

let lemma_mod_add_last c12 t4' =
  let r4 = c12 +. t4' in
  assert (v c12 + v t4' < pow2 48 + pow2 48);
  Math.Lemmas.pow2_double_sum 48;
  assert (v c12 + v t4' < pow2 49);
  Math.Lemmas.pow2_lt_compat 64 49;
  Math.Lemmas.small_mod (v c12 + v t4') (pow2 64);
  assert (v r4 = v c12 + v t4')


///  squaring

val lemma_mul_by2: m:nat -> max:nat -> a:uint64 -> Lemma
  (requires v a <= m * max /\ 2 * m <= 4096 /\ max <= max52)
  (ensures  (let r = a *. u64 2 in
    v r = v a * 2 /\ v r <= (2 * m) * max))

let lemma_mul_by2 m max a =
  let r = a *. u64 2 in
  calc (<=) {
    v a * 2;
    (<=) { Math.Lemmas.lemma_mult_le_right 2 (v a) (m * max) }
    m * max * 2;
    (==) { Math.Lemmas.swap_mul (m * max) 2 }
    2 * (m * max);
    (==) { Math.Lemmas.paren_mul_right 2 m max }
    2 * m * max;
    };
  assert (v a * 2 <= 2 * m * max);

  ML.lemma_ab_le_cd (2 * m) max 4096 max52;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a * 2) (pow2 64)


val lemma_four_sqr64_wide (a0 a1 a2 a3:uint64) : Lemma
  (requires
    felem_fits1 a0 64 /\ felem_fits1 a1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 a3 64)
  (ensures
   (let d = mul64_wide (a0 *. u64 2) a3 +. mul64_wide (a1 *. u64 2) a2 in
    v d = v a0 * v a3 + v a1 * v a2 + v a2 * v a1 + v a3 * v a0 /\
    v d <= 16384 * (max52 * max52)))

let lemma_four_sqr64_wide a0 a1 a2 a3 =
  let r0 = a0 *. u64 2 in
  let r1 = a1 *. u64 2 in
  lemma_mul_by2 64 max52 a0;
  lemma_mul_by2 64 max52 a1;
  assert (v r0 = v a0 * 2 /\ v r1 = v a1 * 2);

  lemma_bound_mul64_wide 128 64 max52 max52 r0 a3;
  lemma_bound_mul64_wide 128 64 max52 max52 r1 a2;
  assert (v a0 * 2 * v a3 + v a1 * 2 * v a2 <= 16384 * (max52 * max52));
  assert_norm (16384 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v a0 * 2 * v a3 + v a1 * 2 * v a2) (pow2 128);
  calc (==) {
    v a0 * 2 * v a3 + v a1 * 2 * v a2;
    (==) { Math.Lemmas.swap_mul (v a0) 2; Math.Lemmas.paren_mul_right 2 (v a0) (v a3) }
    v a0 * v a3 + v a0 * v a3 + v a1 * 2 * v a2;
    (==) { Math.Lemmas.swap_mul (v a1) 2; Math.Lemmas.paren_mul_right 2 (v a1) (v a2) }
    v a0 * v a3 + v a0 * v a3 + v a1 * v a2 + v a2 * v a1;
  }


val lemma_add_five_sqr64_wide (md:nat) (d:uint128) (a0 a1 a2 a3 a4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 16385 /\
    felem_fits1 a0 64 /\ felem_fits1 a1 64 /\
    felem_fits1 a2 64 /\ felem_fits1 a3 64 /\
    felem_fits_last1 a4 64)
  (ensures
   (let d1 = d +. mul64_wide a0 (a4 *. u64 2) +. mul64_wide (a1 *. u64 2) a3 +. mul64_wide a2 a2 in
    v d1 == v d + v a0 * v a4 + v a1 * v a3 + v a2 * v a2 + v a3 * v a1 + v a4 * v a0 /\
    v d1 <= 12801 * (max52 * max52)))

let lemma_add_five_sqr64_wide md d a0 a1 a2 a3 a4 =
  let r4 = a4 *. u64 2 in
  let r1 = a1 *. u64 2 in
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;
  lemma_mul_by2 64 max52 a1;
  assert (v r4 = v a4 * 2 /\ v r1 = v a1 * 2);

  lemma_bound_mul64_wide 64 128 max52 max48 a0 r4;
  lemma_bound_mul64_wide 128 64 max52 max52 r1 a3;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 a2;
  assert (v d + v a0 * (v a4 * 2) + v a1 * 2 * v a3 + v a2 * v a2 <=
    md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52);
    (<=) { lemma_16_max52_max48 512 }
    md * max52 + 512 * (max52 * max52) + 12288 * (max52 * max52);
    (<) { assert_norm (16385 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 12800 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 12800 }
    12801 * (max52 * max52);
    };

  assert_norm (12801 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2) + v a1 * 2 * v a3) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2) + v a1 * 2 * v a3 + v a2 * v a2) (pow2 128);

  calc (==) {
    v d + v a0 * (v a4 * 2) + v a1 * 2 * v a3 + v a2 * v a2;
    (==) { Math.Lemmas.swap_mul (v a1) 2; Math.Lemmas.paren_mul_right 2 (v a1) (v a3) }
    v d + v a0 * (v a4 * 2) + v a1 * v a3 + v a1 * v a3 + v a2 * v a2;
    (==) { Math.Lemmas.paren_mul_right (v a0) (v a4) 2; Math.Lemmas.swap_mul 2 (v a0 * v a4) }
    v d + v a0 * v a4 + v a0 * v a4 + v a1 * v a3 + v a1 * v a3 + v a2 * v a2;
  }


val lemma_add_four_sqr64_wide (md:nat) (d:uint128) (a1 a2 a3 a4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 12802 /\
    felem_fits1 a1 64 /\ felem_fits1 a2 64 /\
    felem_fits1 a3 64 /\ felem_fits_last1 a4 64)
  (ensures
   (let d1 = d +. mul64_wide a1 (a4 *. u64 2) +. mul64_wide (a2 *. u64 2) a3 in
    v d1 == v d + v a1 * v a4 + v a2 * v a3 + v a3 * v a2 + v a4 * v a1 /\
    v d1 <= 8705 * (max52 * max52)))

let lemma_add_four_sqr64_wide md d a1 a2 a3 a4 =
  let r4 = a4 *. u64 2 in
  let r2 = a2 *. u64 2 in
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;
  lemma_mul_by2 64 max52 a2;
  assert (v r2 = v a2 * 2 /\ v r4 = v a4 * 2);

  let d1 = d +. mul64_wide a1 r4 +. mul64_wide r2 a3 in
  lemma_bound_mul64_wide 64 128 max52 max48 a1 (a4 *. u64 2);
  lemma_bound_mul64_wide 128 64 max52 max52 (a2 *. u64 2) a3;
  assert (v d + v a1 * (v a4 * 2) + v a2 * 2 * v a3 <=
    md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52);
    (<=) { lemma_16_max52_max48 512 }
    md * max52 + 512 * (max52 * max52) + 8192 * (max52 * max52);
    (<) { assert_norm (12802 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 8704 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 8704 }
    8705 * (max52 * max52);
    };
  assert_norm (8705 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * (2 * v a4)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * (2 * v a4) + (v a2 * 2) * v a3) (pow2 128);

  calc (==) {
    v d + v a1 * (2 * v a4) + (v a2 * 2) * v a3;
    (==) { Math.Lemmas.swap_mul (v a2) 2; Math.Lemmas.paren_mul_right 2 (v a2) (v a3) }
    v d + v a1 * (2 * v a4) + v a2 * v a3 + v a3 * v a2;
    (==) { Math.Lemmas.swap_mul (v a1) (2 * v a4); Math.Lemmas.paren_mul_right 2 (v a4) (v a1) }
    v d + v a1 * v a4 + v a4 * v a1 + v a2 * v a3 + v a3 * v a2;
    }


val lemma_add_two_sqr64_wide52 (md:nat) (d:uint128) (a0 a1:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 4097 /\
    felem_fits1 a0 64 /\ felem_fits1 a1 64)
  (ensures
   (let d1 = d +. mul64_wide (a0 *. u64 2) a1 in
    v d1 == v d + v a0 * v a1 + v a1 * v a0 /\
    v d1 <= 8193 * (max52 * max52)))

let lemma_add_two_sqr64_wide52 md d a0 a1 =
  lemma_mul_by2 64 max52 a0;
  lemma_bound_mul64_wide 128 64 max52 max52 (a0 *. u64 2) a1;
  assert (v d + v a0 * 2 * v a1 <= md * max52 + 8192 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max52);
    (<) { assert_norm (4097 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 8192 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 8192 }
    8193 * (max52 * max52);
    };
  assert_norm (8193 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * 2 * v a1) (pow2 128)


val lemma_add_three_sqr64_wide (md:nat) (d:uint128) (a2 a3 a4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 8705 /\
    felem_fits1 a2 64 /\ felem_fits1 a3 64 /\
    felem_fits_last1 a4 64)
  (ensures
   (let d1 = d +. mul64_wide a2 (a4 *. u64 2) +. mul64_wide a3 a3 in
    v d1 == v d + v a2 * v a4 + v a3 * v a3 + v a4 * v a2 /\
    v d1 <= 4609 * (max52 * max52)))

let lemma_add_three_sqr64_wide md d a2 a3 a4 =
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;

  lemma_bound_mul64_wide 64 128 max52 max48 a2 (a4 *. u64 2);
  lemma_bound_mul64_wide 64 64 max52 max52 a3 a3;
  assert (v d + v a2 * (v a4 * 2) + v a3 * v a3 <=
    md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52));

  calc (<) {
    md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52);
    (<=) { lemma_16_max52_max48 512 }
    md * max52 + 512 * (max52 * max52) + 4096 * (max52 * max52);
    (<) { assert_norm (8705 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 4608 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 4608 }
    4609 * (max52 * max52);
    };
  assert_norm (4609 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a2 * (v a4 * 2)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a2 * (v a4 * 2) + v a3 * v a3) (pow2 128);

  calc (==) {
    v d + v a2 * (v a4 * 2) + v a3 * v a3;
    (==) { Math.Lemmas.paren_mul_right (v a2) (v a4) 2 }
    v d + v a2 * v a4 + v a4 * v a2 + v a3 * v a3;
  }


val lemma_add_three_sqr64_wide52 (md:nat) (d:uint128) (a0 a1 a2:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 8194 /\
    felem_fits1 a0 64 /\ felem_fits1 a1 64 /\
    felem_fits1 a2 64)
  (ensures
   (let d1 = d +. mul64_wide (a0 *. u64 2) a2 +. mul64_wide a1 a1 in
    v d1 == v d + v a0 * v a2 + v a1 * v a1 + v a2 * v a0 /\
    v d1 <= 12289 * (max52 * max52)))

let lemma_add_three_sqr64_wide52 md d a0 a1 a2 =
  lemma_mul_by2 64 max52 a0;
  lemma_bound_mul64_wide 128 64 max52 max52 (a0 *. u64 2) a2;
  lemma_bound_mul64_wide 64 64 max52 max52 a1 a1;
  assert (v d + v a0 * v a2 + v a1 * v a1 + v a2 * v a0 <=
    md * max52 + 12288 * (max52 * max52));

  calc (<) {
    md * max52 + 12288 * (max52 * max52);
    (<) { assert_norm (8194 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 12288 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 12288 }
    12289 * (max52 * max52);
    };
  assert_norm (12289 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * 2 * v a2) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * 2 * v a2 + v a1 * v a1) (pow2 128);

  calc (==) {
    v d + v a0 * 2 * v a2 + v a1 * v a1;
    (==) { Math.Lemmas.swap_mul (v a0) 2; Math.Lemmas.paren_mul_right 2 (v a0) (v a2) }
    v d + v a0 * v a2 + v a2 * v a0 + v a1 * v a1;
  }


val lemma_add_two_sqr64_wide (md:nat) (d:uint128) (a3 a4:uint64) : Lemma
  (requires
    v d <= md * max52 /\ md <= 64193 /\
    felem_fits1 a3 64 /\ felem_fits_last1 a4 64)
  (ensures
   (let d1 = d +. mul64_wide a3 (a4 *. u64 2) in
    v d1 == v d + v a3 * v a4 + v a4 * v a3 /\
    v d1 <= 513 * (max52 * max52)))

let lemma_add_two_sqr64_wide md d a3 a4 =
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;
  lemma_bound_mul64_wide 64 128 max52 max48 a3 (a4 *. u64 2);
  assert (v d + v a3 * (v a4 * 2) <= md * max52 + 8192 * (max52 * max48));

  calc (<) {
    md * max52 + 8192 * (max52 * max48);
    (<=) { lemma_16_max52_max48 512 }
    md * max52 + 512 * (max52 * max52);
    (<) { assert_norm (64193 < max52); Math.Lemmas.lemma_mult_lt_right max52 md max52 }
    max52 * max52 + 512 * (max52 * max52);
    (==) { Math.Lemmas.distributivity_add_left (max52 * max52) 1 512 }
    513 * (max52 * max52);
    };
  assert_norm (513 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a3 * (v a4 * 2)) (pow2 128)
