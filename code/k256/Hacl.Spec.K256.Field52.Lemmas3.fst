module Hacl.Spec.K256.Field52.Lemmas3

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module L4 = Hacl.Spec.K256.Field52.Lemmas4
open Hacl.Spec.K256.Field52.Lemmas5

#set-options "--z3rlimit 150 --fuel 0 --ifuel 0"

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
