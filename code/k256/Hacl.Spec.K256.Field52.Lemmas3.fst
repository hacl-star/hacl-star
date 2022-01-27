module Hacl.Spec.K256.Field52.Lemmas3

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas
module L4 = Hacl.Spec.K256.Field52.Lemmas4


#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"


val lemma_bound_mul64_wide (ma mb:nat) (mma mmb:nat) (a b:uint64) : Lemma
  (requires v a <= ma * mma /\ v b <= mb * mmb)
  (ensures  (let r = mul64_wide a b in
    v r = v a * v b /\ v r <= ma * mb * (mma * mmb)))

let lemma_bound_mul64_wide ma mb mma mmb a b =
  let r = mul64_wide a b in
  assert (v r = v a * v b);
  calc (<=) {
    v a * v b;
    (<=) { Math.Lemmas.lemma_mult_le_right (v b) (v a) (ma * mma) }
    (ma * mma) * v b;
    (<=) { Math.Lemmas.lemma_mult_le_left (ma * mma) (v b) (mb * mmb) }
    (ma * mma) * (mb * mmb);
    (==) { Math.Lemmas.paren_mul_right ma mma (mb * mmb) }
    ma * (mma * (mb * mmb));
    (==) {
      Math.Lemmas.paren_mul_right mma mb mmb;
      Math.Lemmas.swap_mul mma mb;
      Math.Lemmas.paren_mul_right mb mma mmb }
    ma * (mb * (mma * mmb));
    (==) { Math.Lemmas.paren_mul_right ma mb (mma * mmb) }
    ma * mb * (mma * mmb);
  }


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


val lemma_16_max52_max48: unit -> Lemma (16 * (max52 * max48) < max52 * max52)
let lemma_16_max52_max48 () =
  assert_norm (16 * (max52 * max48) < max52 * max52)


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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52) <= 12801 * (max52 * max52));
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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52) <= 8705 * (max52 * max52));
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
  assert (v d + v a0 * v b2 + v a1 * v b1 + v a2 * v b0 <= md * max52 + 12288 * (max52 * max52));
  assert_norm (md * max52 + 12288 * (max52 * max52) <= 12289 * (max52 * max52));
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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52) <= 4609 * (max52 * max52));
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
  assert_norm (md * max52 + 8192 * (max52 * max52) <= 8193 * (max52 * max52));
  assert_norm (md * max52 + 8192 * (max52 * max52) < pow2 128);
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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) <= 513 * (max52 * max52));
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
  Math.Lemmas.lemma_mult_le_right (pow2 12) 0x1000003D10 (pow2 37);
  Math.Lemmas.pow2_plus 12 37;
  assert (0x1000003D10 * pow2 12 < pow2 49);
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
  Math.Lemmas.pow2_plus pa pb;
  Math.Lemmas.pow2_le_compat 103 (pa + pb);
  assert_norm (pow2 103 < max52 * max52);
  assert (v d + v a * v b <= md * (max52 * max52) + max52 * max52);
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

  let r = c +. mul64_wide rs d in
  lemma_bound_mul64_wide 1 1 (pow2 49) (pow2 50) rs d;
  assert (v c + v rs * v d + v t3 < md * max52 + pow2 49 * pow2 50 + max52);
  Math.Lemmas.pow2_plus 49 50;
  assert (v c + v rs * v d + v t3 < md * max52 + pow2 99 + max52);
  Math.Lemmas.distributivity_add_left md 1 max52;
  assert (v c + v rs * v d + v t3 < (md + 1) * max52 + pow2 99);
  Math.Lemmas.lemma_mult_le_right max52 (md + 1) 12291;
  assert_norm (12291 * max52 < pow2 99);
  Math.Lemmas.pow2_double_sum 99;
  assert (12291 * max52 + pow2 99 < pow2 100);
  Math.Lemmas.pow2_lt_compat 128 100;
  Math.Lemmas.small_mod (v c + v rs * v d + v t3) (pow2 128);
  assert (v rs = 0x1000003D10 * pow2 12)


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
  Math.Lemmas.lemma_mult_le_left max48 max48 (pow2 48);
  Math.Lemmas.lemma_mult_le_right (pow2 48) max48 (pow2 48);
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
  Math.Lemmas.lemma_mult_le_left max52 max52 (pow2 52);
  Math.Lemmas.lemma_mult_le_right (pow2 52) max52 (pow2 52);
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
  Math.Lemmas.lemma_mult_le_right (pow2 4) (v u0) (pow2 52 - 1);
  Math.Lemmas.distributivity_sub_left (pow2 52) 1 (pow2 4);
  Math.Lemmas.pow2_plus 52 4;
  assert (v u0 * pow2 4 <= pow2 56 - pow2 4);
  Math.Lemmas.pow2_lt_compat 64 56;
  Math.Lemmas.small_mod (v u0 * pow2 4) (pow2 64);
  assert (v (u0 <<. 4ul) = v u0 * pow2 4 % pow2 64);

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


#set-options "--z3rlimit 150"

val fmul5_lemma: a:felem5 -> b:felem5 -> Lemma
  (requires
    felem_fits5 a (64,64,64,64,64) /\
    felem_fits5 b (64,64,64,64,64))
  (ensures (let res = fmul5 a b in
    as_nat5 res % S.prime == as_nat5 a * as_nat5 b % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))

let fmul5_lemma a b =
  let (a0,a1,a2,a3,a4) = a in
  let (b0,b1,b2,b3,b4) = b in

  let r = u64 0x1000003D10 in

  let d0 = mul64_wide a0 b3
       +. mul64_wide a1 b2
       +. mul64_wide a2 b1
       +. mul64_wide a3 b0 in
  lemma_four_mul64_wide a0 a1 a2 a3 b0 b1 b2 b3;
  assert (v d0 = v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0);
  assert (v d0 <= 16384 * (max52 * max52));

  let c0 = mul64_wide a4 b4 in
  lemma_bound_mul64_wide 64 64 max48 max48 a4 b4;
  assert (v c0 = v a4 * v b4);
  assert (v c0 <= 4096 * (max48 * max48));

  let d1 = d0 +. mul64_wide r (to_u64 c0) in let c1 = to_u64 (c0 >>. 64ul) in
  lemma_bound_add_mul64_wide_r 16384 d0 c0;
  assert (v d1 = v d0 + v r * (v c0 % pow2 64));
  assert (v d1 <= 16385 * (max52 * max52));
  lemma_bound_rsh64_to c0;
  assert (v c1 = v c0 / pow2 64);
  lemma_bound_c0 c0;
  assert (v c1 <= pow2 44);

  let t3 = to_u64 d1 &. mask52 in let d2 = d1 >>. 52ul in
  lemma_bound_mask52_rsh52 16385 d1;
  assert (v t3 = v d1 % pow2 52);
  assert (felem_fits1 t3 1);
  assert (v d2 = v d1 / pow2 52);
  assert (v d2 <= 16385 * max52);

  let d3 = d2
       +. mul64_wide a0 b4
       +. mul64_wide a1 b3
       +. mul64_wide a2 b2
       +. mul64_wide a3 b1
       +. mul64_wide a4 b0 in
  lemma_add_five_mul64_wide 16385 d2 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4;
  assert (v d3 == v d2 + v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0);
  assert (v d3 <= 12801 * (max52 * max52));

  let d4 = d3 +. mul64_wide (r <<. 12ul) c1 in
  lemma_bound_add_mul64_wide_r_lsh12 12801 d3 c1;
  assert (v d4 == v d3 + v r * pow2 12 * v c1);
  assert (v d4 <= 12802 * (max52 * max52));

  let t4 = to_u64 d4 &. mask52 in let d5 = d4 >>. 52ul in
  lemma_bound_mask52_rsh52 12802 d4;
  assert (v t4 = v d4 % pow2 52);
  assert (felem_fits1 t4 1);
  assert (v d5 = v d4 / pow2 52);
  assert (v d5 <= 12802 * max52);

  let tx = t4 >>. 48ul in let t4' = t4 &. mask48 in
  lemma_bound_mask48_rsh48 t4;
  assert (v tx = v t4 / pow2 48);
  assert (v tx < pow2 4);
  assert (v t4' = v t4 % pow2 48);
  assert (felem_fits_last1 t4' 1);

  let c2 = mul64_wide a0 b0 in
  lemma_bound_mul64_wide 64 64 max52 max52 a0 b0;
  assert (v c2 = v a0 * v b0);
  assert (v c2 <= 4096 * (max52 * max52));

  let d6 = d5
       +. mul64_wide a1 b4
       +. mul64_wide a2 b3
       +. mul64_wide a3 b2
       +. mul64_wide a4 b1 in
  lemma_add_four_mul64_wide 12802 d5 a1 a2 a3 a4 b1 b2 b3 b4;
  assert (v d6 == v d5 + v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1);
  assert (v d6 <= 8705 * (max52 * max52));

  let u0 = to_u64 d6 &. mask52 in let d7 = d6 >>. 52ul in
  lemma_bound_mask52_rsh52 8705 d6;
  assert (v u0 = v d6 % pow2 52);
  assert (felem_fits1 u0 1);
  assert (v d7 = v d6 / pow2 52);
  assert (v d7 <= 8705 * max52);

  let u0' = tx |. (u0 <<. 4ul) in
  lemma_tx_logor_u0_lsh4 tx u0;
  assert (v u0' == v tx + v u0 * pow2 4);
  assert (v u0' < pow2 56);

  let c3 = c2 +. mul64_wide u0' (r >>. 4ul) in
  lemma_bound_add_mul64_wide_r_rsh4 4096 c2 u0';
  assert (v c3 = v c2 + v u0' * (v r / pow2 4));
  assert (v c3 <= 4097 * (max52 * max52));

  let r0 = to_u64 c3 &. mask52 in let c4 = c3 >>. 52ul in
  lemma_bound_mask52_rsh52 4097 c3;
  assert (v r0 = v c3 % pow2 52);
  assert (felem_fits1 r0 1);
  assert (v c4 = v c3 / pow2 52);
  assert (v c4 <= 4097 * max52);

  let c5 = c4
       +. mul64_wide a0 b1
       +. mul64_wide a1 b0 in
  lemma_add_two_mul64_wide52 4097 c4 a0 a1 b0 b1;
  assert (v c5 = v c4 + v a0 * v b1 + v a1 * v b0);
  assert (v c5 <= 8193 * (max52 * max52));

  let d8 = d7
       +. mul64_wide a2 b4
       +. mul64_wide a3 b3
       +. mul64_wide a4 b2 in
  lemma_add_three_mul64_wide 8705 d7 a2 a3 a4 b2 b3 b4;
  assert (v d8 = v d7 + v a2 * v b4 + v a3 * v b3 + v a4 * v b2);
  assert (v d8 <= 4609 * (max52 * max52));

  let c6 = c5 +. mul64_wide (to_u64 d8 &. mask52) r in let d9 = d8 >>. 52ul in
  lemma_bound_add_mul64_wide_r_mask52 8193 d8 c5;
  assert (v d9 = v d8 / pow2 52);
  assert (v d9 <= 8193 * max52);
  assert (v c6 = v c5 + v d8 % pow2 52 * v r);
  assert (v c6 <= 8194 * (max52 * max52));

  let r1 = to_u64 c6 &. mask52 in let c7 = c6 >>. 52ul in
  lemma_bound_mask52_rsh52 8194 c6;
  assert (v r1 = v c6 % pow2 52);
  assert (felem_fits1 r1 1);
  assert (v c7 = v c6 / pow2 52);
  assert (v c7 <= 8194 * max52);

  let c8 = c7
       +. mul64_wide a0 b2
       +. mul64_wide a1 b1
       +. mul64_wide a2 b0 in
  lemma_add_three_mul64_wide52 8194 c7 a0 a1 a2 b0 b1 b2;
  assert (v c8 == v c7 + v a0 * v b2 + v a1 * v b1 + v a2 * v b0);
  assert (v c8 <= 12289 * (max52 * max52));

  let d10 = d9
       +. mul64_wide a3 b4
       +. mul64_wide a4 b3 in
  lemma_add_two_mul64_wide 8193 d9 a3 a4 b3 b4;
  assert (v d10 == v d9 + v a3 * v b4 + v a4 * v b3);
  assert (v d10 <= 513 * (max52 * max52));

  let c9 = c8 +. mul64_wide r (to_u64 d10) in let d11 = to_u64 (d10 >>. 64ul) in
  lemma_bound_add_mul64_wide_r 12289 c8 d10;
  assert (v c9 = v c8 + v r * (v d10 % pow2 64));
  assert (v c9 <= 12290 * (max52 * max52));
  lemma_bound_rsh64_to d10;
  assert (v d11 = v d10 / pow2 64);
  lemma_bound_d10 d10;
  assert (v d11 < pow2 50);

  let r2 = to_u64 c9 &. mask52 in let c10 = c9 >>. 52ul in
  lemma_bound_mask52_rsh52 12290 c9;
  assert (v r2 = v c9 % pow2 52);
  assert (felem_fits1 r2 1);
  assert (v c10 = v c9 / pow2 52);
  assert (v c10 <= 12290 * max52);

  let c11 = c10 +. mul64_wide (r <<. 12ul) d11 +. to_u128 t3 in
  lemma_bound_add_mul64_wide_r_lsh12_add 12290 c10 d11 t3;
  assert (v c11 = v c10 + v r * pow2 12 * v d11 + v t3);
  assert (v c11 < pow2 100);

  let r3 = to_u64 c11 &. mask52 in let c12 = to_u64 (c11 >>. 52ul) in
  lemma_bound_mask52_rsh52_sp c11;
  assert (v r3 = v c11 % pow2 52);
  assert (felem_fits1 r3 1);
  assert (v c12 = v c11 / pow2 52);
  assert (v c12 < pow2 48);

  let r4 = c12 +. t4' in
  lemma_mod_add_last c12 t4';
  assert (v r4 = v c12 + v t4');
  assert (felem_fits_last1 r4 2);

  let res = (r0,r1,r2,r3,r4) in
  assert (res == fmul5 a b);
  assert (felem_fits5 res (1,1,1,1,2));

  L4.lemma_fmul_simplify (v r0) (v r1) (v r2) (v r3) (v r4)
    (v c3) (v c6) (v c9) (v c11) (v d4) (v d8) (v d10) (v d11)
    (v t3) (v a0) (v a1) (v a2) (v a3) (v a4) (v b0) (v b1) (v b2) (v b3) (v b4)


///  squaring

val lemma_mul_by2: m:nat -> max:nat -> a:uint64 -> Lemma
  (requires v a <= m * max /\ 2 * m <= 4096 /\ max <= max52)
  (ensures  (let r = a *. u64 2 in
    v r = v a * 2 /\ v r <= (2 * m) * max))

let lemma_mul_by2 m max a =
  let r = a *. u64 2 in
  Math.Lemmas.lemma_mult_le_right 2 (v a) (m * max);
  assert (v a * 2 <= m * max * 2);
  Math.Lemmas.swap_mul (m * max) 2;
  Math.Lemmas.paren_mul_right m max 2;
  assert (v a * 2 <= 2 * m * max);
  Math.Lemmas.lemma_mult_le_right max (2 * m) 4096;
  assert (2 * m * max <= 4096 * max);
  Math.Lemmas.lemma_mult_le_left 4096 max max52;
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
  lemma_mul_by2 64 max52 a0;
  lemma_mul_by2 64 max52 a1;
  lemma_bound_mul64_wide 128 64 max52 max52 (a0 *. u64 2) a3;
  lemma_bound_mul64_wide 128 64 max52 max52 (a1 *. u64 2) a2;
  assert (v a0 * 2 * v a3 + v a1 * 2 * v a2 <= 16384 * (max52 * max52));
  assert_norm (16384 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v a0 * 2 * v a3 + v a1 * 2 * v a2) (pow2 128)


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
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;
  lemma_mul_by2 64 max52 a1;

  lemma_bound_mul64_wide 64 128 max52 max48 a0 (a4 *. u64 2);
  lemma_bound_mul64_wide 128 64 max52 max52 (a1 *. u64 2) a3;
  lemma_bound_mul64_wide 64 64 max52 max52 a2 a2;
  //Math.Lemmas.swap_mul max52 max48;
  assert (v d + v a0 * (v a4 * 2) + v a1 * 2 * v a3 + v a2 * v a2 <=
    md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52));
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 12288 * (max52 * max52) <= 12801 * (max52 * max52));
  assert_norm (12801 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2) + (v a1 * 2) * v a3) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * (v a4 * 2) + (v a1 * 2) * v a3 + v a2 * v a2) (pow2 128)


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
  assert_norm (max48 < max52);
  lemma_mul_by2 64 max48 a4;
  lemma_mul_by2 64 max52 a2;

  lemma_bound_mul64_wide 64 128 max52 max48 a1 (a4 *. u64 2);
  lemma_bound_mul64_wide 128 64 max52 max52 (a2 *. u64 2) a3;
  assert (v d + v a1 * (v a4 * 2) + v a2 * 2 * v a3 <=
    md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52));
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 8192 * (max52 * max52) <= 8705 * (max52 * max52));
  assert_norm (8705 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a1 * (2 * v a4)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a1 * (2 * v a4) + (v a2 * 2) * v a3) (pow2 128)


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
  assert_norm (md * max52 + 8192 * (max52 * max52) <= 8193 * (max52 * max52));
  assert_norm (md * max52 + 8192 * (max52 * max52) < pow2 128);
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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) + 4096 * (max52 * max52) <= 4609 * (max52 * max52));
  assert_norm (4609 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a2 * (v a4 * 2)) (pow2 128);
  Math.Lemmas.small_mod (v d + v a2 * (v a4 * 2) + v a3 * v a3) (pow2 128)


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
  assert (v d + v a0 * v a2 + v a1 * v a1 + v a2 * v a0 <= md * max52 + 12288 * (max52 * max52));
  assert_norm (md * max52 + 12288 * (max52 * max52) <= 12289 * (max52 * max52));
  assert_norm (12289 * (max52 * max52) < pow2 128);

  Math.Lemmas.small_mod (v d + v a0 * 2 * v a2) (pow2 128);
  Math.Lemmas.small_mod (v d + v a0 * 2 * v a2 + v a1 * v a1) (pow2 128)


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
  lemma_16_max52_max48 ();
  assert_norm (md * max52 + 8192 * (max52 * max48) <= 513 * (max52 * max52));
  assert_norm (513 * (max52 * max52) < pow2 128);
  Math.Lemmas.small_mod (v d + v a3 * (v a4 * 2)) (pow2 128)


val fsqr5_lemma: a:felem5 -> Lemma
  (requires
    felem_fits5 a (64,64,64,64,64))
  (ensures (let res = fsqr5 a in
    as_nat5 res % S.prime == as_nat5 a * as_nat5 a % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))

let fsqr5_lemma a =
  let (a0,a1,a2,a3,a4) = a in

  let r = u64 0x1000003D10 in

  let d0 = mul64_wide (a0 *. u64 2) a3 +. mul64_wide (a1 *. u64 2) a2 in
  lemma_four_sqr64_wide a0 a1 a2 a3;
  assert (v d0 = v a0 * v a3 + v a1 * v a2 + v a2 * v a1 + v a3 * v a0);
  assert (v d0 <= 16384 * (max52 * max52));

  let c0 = mul64_wide a4 a4 in
  lemma_bound_mul64_wide 64 64 max48 max48 a4 a4;
  assert (v c0 = v a4 * v a4);
  assert (v c0 <= 4096 * (max48 * max48));

  let d1 = d0 +. mul64_wide r (to_u64 c0) in let c1 = to_u64 (c0 >>. 64ul) in
  lemma_bound_add_mul64_wide_r 16384 d0 c0;
  assert (v d1 = v d0 + v r * (v c0 % pow2 64));
  assert (v d1 <= 16385 * (max52 * max52));
  lemma_bound_rsh64_to c0;
  assert (v c1 = v c0 / pow2 64);
  lemma_bound_c0 c0;
  assert (v c1 <= pow2 44);

  let t3 = to_u64 d1 &. mask52 in let d2 = d1 >>. 52ul in
  lemma_bound_mask52_rsh52 16385 d1;
  assert (v t3 = v d1 % pow2 52);
  assert (felem_fits1 t3 1);
  assert (v d2 = v d1 / pow2 52);
  assert (v d2 <= 16385 * max52);

  let d3 = d2
       +. mul64_wide a0 (a4 *. u64 2)
       +. mul64_wide (a1 *. u64 2) a3
       +. mul64_wide a2 a2 in
  lemma_add_five_sqr64_wide 16385 d2 a0 a1 a2 a3 a4;
  assert (v d3 == v d2 + v a0 * v a4 + v a1 * v a3 + v a2 * v a2 + v a3 * v a1 + v a4 * v a0);
  assert (v d3 <= 12801 * (max52 * max52));

  let d4 = d3 +. mul64_wide (r <<. 12ul) c1 in
  lemma_bound_add_mul64_wide_r_lsh12 12801 d3 c1;
  assert (v d4 == v d3 + v r * pow2 12 * v c1);
  assert (v d4 <= 12802 * (max52 * max52));

  let t4 = to_u64 d4 &. mask52 in let d5 = d4 >>. 52ul in
  lemma_bound_mask52_rsh52 12802 d4;
  assert (v t4 = v d4 % pow2 52);
  assert (felem_fits1 t4 1);
  assert (v d5 = v d4 / pow2 52);
  assert (v d5 <= 12802 * max52);

  let tx = t4 >>. 48ul in let t4' = t4 &. mask48 in
  lemma_bound_mask48_rsh48 t4;
  assert (v tx = v t4 / pow2 48);
  assert (v tx < pow2 4);
  assert (v t4' = v t4 % pow2 48);
  assert (felem_fits_last1 t4' 1);

  let c2 = mul64_wide a0 a0 in
  lemma_bound_mul64_wide 64 64 max52 max52 a0 a0;
  assert (v c2 = v a0 * v a0);
  assert (v c2 <= 4096 * (max52 * max52));

  let d6 = d5
       +. mul64_wide a1 (a4 *. u64 2)
       +. mul64_wide (a2 *. u64 2) a3 in
  lemma_add_four_sqr64_wide 12802 d5 a1 a2 a3 a4;
  assert (v d6 == v d5 + v a1 * v a4 + v a2 * v a3 + v a3 * v a2 + v a4 * v a1);
  assert (v d6 <= 8705 * (max52 * max52));

  let u0 = to_u64 d6 &. mask52 in let d7 = d6 >>. 52ul in
  lemma_bound_mask52_rsh52 8705 d6;
  assert (v u0 = v d6 % pow2 52);
  assert (felem_fits1 u0 1);
  assert (v d7 = v d6 / pow2 52);
  assert (v d7 <= 8705 * max52);

  let u0' = tx |. (u0 <<. 4ul) in
  lemma_tx_logor_u0_lsh4 tx u0;
  assert (v u0' == v tx + v u0 * pow2 4);
  assert (v u0' < pow2 56);

  let c3 = c2 +. mul64_wide u0' (r >>. 4ul) in
  lemma_bound_add_mul64_wide_r_rsh4 4096 c2 u0';
  assert (v c3 = v c2 + v u0' * (v r / pow2 4));
  assert (v c3 <= 4097 * (max52 * max52));

  let r0 = to_u64 c3 &. mask52 in let c4 = c3 >>. 52ul in
  lemma_bound_mask52_rsh52 4097 c3;
  assert (v r0 = v c3 % pow2 52);
  assert (felem_fits1 r0 1);
  assert (v c4 = v c3 / pow2 52);
  assert (v c4 <= 4097 * max52);

  let c5 = c4 +. mul64_wide (a0 *. u64 2) a1 in
  lemma_add_two_sqr64_wide52 4097 c4 a0 a1;
  assert (v c5 = v c4 + v a0 * v a1 + v a1 * v a0);
  assert (v c5 <= 8193 * (max52 * max52));

  let d8 = d7
       +. mul64_wide a2 (a4 *. u64 2)
       +. mul64_wide a3 a3 in
  lemma_add_three_sqr64_wide 8705 d7 a2 a3 a4;
  assert (v d8 = v d7 + v a2 * v a4 + v a3 * v a3 + v a4 * v a2);
  assert (v d8 <= 4609 * (max52 * max52));

  let c6 = c5 +. mul64_wide (to_u64 d8 &. mask52) r in let d9 = d8 >>. 52ul in
  lemma_bound_add_mul64_wide_r_mask52 8193 d8 c5;
  assert (v d9 = v d8 / pow2 52);
  assert (v d9 <= 8193 * max52);
  assert (v c6 = v c5 + v d8 % pow2 52 * v r);
  assert (v c6 <= 8194 * (max52 * max52));

  let r1 = to_u64 c6 &. mask52 in let c7 = c6 >>. 52ul in
  lemma_bound_mask52_rsh52 8194 c6;
  assert (v r1 = v c6 % pow2 52);
  assert (felem_fits1 r1 1);
  assert (v c7 = v c6 / pow2 52);
  assert (v c7 <= 8194 * max52);

  let c8 = c7
       +. mul64_wide (a0 *. u64 2) a2
       +. mul64_wide a1 a1 in
  lemma_add_three_sqr64_wide52 8194 c7 a0 a1 a2;
  assert (v c8 == v c7 + v a0 * v a2 + v a1 * v a1 + v a2 * v a0);
  assert (v c8 <= 12289 * (max52 * max52));

  let d10 = d9
       +. mul64_wide a3 (a4 *. u64 2) in
  lemma_add_two_sqr64_wide 8193 d9 a3 a4;
  assert (v d10 == v d9 + v a3 * v a4 + v a4 * v a3);
  assert (v d10 <= 513 * (max52 * max52));

  let c9 = c8 +. mul64_wide r (to_u64 d10) in let d11 = to_u64 (d10 >>. 64ul) in
  lemma_bound_add_mul64_wide_r 12289 c8 d10;
  assert (v c9 = v c8 + v r * (v d10 % pow2 64));
  assert (v c9 <= 12290 * (max52 * max52));
  lemma_bound_rsh64_to d10;
  assert (v d11 = v d10 / pow2 64);
  lemma_bound_d10 d10;
  assert (v d11 < pow2 50);

  let r2 = to_u64 c9 &. mask52 in let c10 = c9 >>. 52ul in
  lemma_bound_mask52_rsh52 12290 c9;
  assert (v r2 = v c9 % pow2 52);
  assert (felem_fits1 r2 1);
  assert (v c10 = v c9 / pow2 52);
  assert (v c10 <= 12290 * max52);

  let c11 = c10 +. mul64_wide (r <<. 12ul) d11 +. to_u128 t3 in
  lemma_bound_add_mul64_wide_r_lsh12_add 12290 c10 d11 t3;
  assert (v c11 = v c10 + v r * pow2 12 * v d11 + v t3);
  assert (v c11 < pow2 100);

  let r3 = to_u64 c11 &. mask52 in let c12 = to_u64 (c11 >>. 52ul) in
  lemma_bound_mask52_rsh52_sp c11;
  assert (v r3 = v c11 % pow2 52);
  assert (felem_fits1 r3 1);
  assert (v c12 = v c11 / pow2 52);
  assert (v c12 < pow2 48);

  let r4 = c12 +. t4' in
  lemma_mod_add_last c12 t4';
  assert (v r4 = v c12 + v t4');
  assert (felem_fits_last1 r4 2);

  let res = (r0,r1,r2,r3,r4) in
  assert (res == fsqr5 a);
  assert (felem_fits5 res (1,1,1,1,2));

  L4.lemma_fmul_simplify (v r0) (v r1) (v r2) (v r3) (v r4)
    (v c3) (v c6) (v c9) (v c11) (v d4) (v d8) (v d10) (v d11)
    (v t3) (v a0) (v a1) (v a2) (v a3) (v a4) (v a0) (v a1) (v a2) (v a3) (v a4)
