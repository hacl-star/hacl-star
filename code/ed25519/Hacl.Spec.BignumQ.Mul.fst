module Hacl.Spec.BignumQ.Mul

open FStar.Mul
open Lib.IntTypes

module S = Spec.Ed25519
module Lemmas = Hacl.Spec.BignumQ.Lemmas

include Hacl.Spec.BignumQ.Definitions


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let mask56 : x:uint64{v x == pow2 56 - 1} =
  assert_norm (pow2 56 - 1 == 0xffffffffffffff);
  u64 0xffffffffffffff


inline_for_extraction noextract
let mask40 : x:uint64{v x == pow2 40 - 1} =
  assert_norm (pow2 40 - 1 == 0xffffffffff);
  u64 0xffffffffff


inline_for_extraction noextract
val make_m: unit -> m:qelem5{qelem_fits5 m (1, 1, 1, 1, 1) /\ as_nat5 m == S.q}
let make_m () =
  let m0 = u64 0x12631a5cf5d3ed in
  let m1 = u64 0xf9dea2f79cd658 in
  let m2 = u64 0x000000000014de in
  let m3 = u64 0x00000000000000 in
  let m4 = u64 0x00000010000000 in
  assert_norm (as_nat5 (m0, m1, m2, m3, m4) == S.q);
  (m0, m1, m2, m3, m4)


inline_for_extraction noextract
val make_mu: unit -> m:qelem5{qelem_fits5 m (1, 1, 1, 1, 1) /\ as_nat5 m == pow2 512 / S.q}
let make_mu m =
  let m0 = u64 0x9ce5a30a2c131b in
  let m1 = u64 0x215d086329a7ed in
  let m2 = u64 0xffffffffeb2106 in
  let m3 = u64 0xffffffffffffff in
  let m4 = u64 0x00000fffffffff in
  assert_norm (as_nat5 (m0, m1, m2, m3, m4) == pow2 512 / S.q);
  (m0, m1, m2, m3, m4)


inline_for_extraction noextract
val choose:
    b:uint64
  -> x:qelem5
  -> y:qelem5 ->
  Pure qelem5
  (requires v b == 0 \/ v b == 1)
  (ensures fun z -> if v b = 1 then z == x else z == y)

let choose b (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let mask = b -. u64 1 in
  let z0 = x0 ^. (mask &. (x0 ^. y0)) in
  Lemmas.lemma_choose_step b x0 y0;
  let z1 = x1 ^. (mask &. (x1 ^. y1)) in
  Lemmas.lemma_choose_step b x1 y1;
  let z2 = x2 ^. (mask &. (x2 ^. y2)) in
  Lemmas.lemma_choose_step b x2 y2;
  let z3 = x3 ^. (mask &. (x3 ^. y3)) in
  Lemmas.lemma_choose_step b x3 y3;
  let z4 = x4 ^. (mask &. (x4 ^. y4)) in
  Lemmas.lemma_choose_step b x4 y4;
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val subm_step: x:uint64 -> y:uint64 ->
  Pure (uint64 & uint64)
  (requires v x < pow56 /\ v y <= pow56)
  (ensures fun (b, t) ->
    v b <= 1 /\ qelem_fits1 t 1 /\
    v x - v y == v t - v b * pow56)

let subm_step x y =
  let b = (x -. y) >>. 63ul in
  //assert (if v x >= v y then v b == 0 else v b == 1);
  let lshift56 = (b <<. 56ul) in
  //assert (if v x >= v y then v lshift56 == 0 else v lshift56 == pow56);
  //assert (v lshift56 == v b * pow56);
  //assert (v ((b <<. 56ul) +! x) == v b * pow56 + v x);
  let t = ((b <<. 56ul) +! x) -! y in
  b, t


inline_for_extraction noextract
val subm_conditional: x:qelem5 ->
  Pure qelem5
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1))
  (ensures fun r ->
    qelem_fits5 r (1, 1, 1, 1, 1) /\
    (if as_nat5 x >= S.q then as_nat5 r == as_nat5 x - S.q else as_nat5 r == as_nat5 x))

let subm_conditional (x0, x1, x2, x3, x4) =
  let (y0, y1, y2, y3, y4) = make_m () in
  let (b0, t0) = subm_step x0 y0 in
  assert (v x0 - v y0 == v t0 - v b0 * pow56);
  let (b1, t1) = subm_step x1 (y1 +! b0) in
  assert (v x1 - v y1 - v b0 == v t1 - v b1 * pow56);
  let (b2, t2) = subm_step x2 (y2 +! b1) in
  assert (v x2 - v y2 - v b1 == v t2 - v b2 * pow56);
  let (b3, t3) = subm_step x3 (y3 +! b2) in
  assert (v x3 - v y3 - v b2 == v t3 - v b3 * pow56);
  let (b4, t4) = subm_step x4 (y4 +! b3) in
  assert (v x4 - v y4 - v b3 == v t4 - v b4 * pow56);

  Lemmas.lemma_subm_conditional
    (v x0) (v x1) (v x2) (v x3) (v x4)
    (v y0) (v y1) (v y2) (v y3) (v y4)
    (v b0) (v b1) (v b2) (v b3) (v b4);

  assert (
    as_nat5 (t0, t1, t2, t3, t4) - v b4 * pow56 * pow224 ==
    as_nat5 (x0, x1, x2, x3, x4) - as_nat5 (y0, y1, y2, y3, y4));

  //assert_norm (pow56 * pow224 = pow2 280);
  //assert (as_nat5 (t0, t1, t2, t3, t4) - v b4 * pow2 280 == as_nat5 (x0, x1, x2, x3, x4) - S.q);
  Lemmas.lemma_as_nat5 (x0, x1, x2, x3, x4);
  Lemmas.lemma_as_nat5 (t0, t1, t2, t3, t4);

  //assert (if v b4 = 0 then as_nat5 (x0, x1, x2, x3, x4) >= S.q else as_nat5 (x0, x1, x2, x3, x4) < S.q);
  assert (if as_nat5 (x0, x1, x2, x3, x4) >= S.q then v b4 == 0 else v b4 == 1);

  let (z0, z1, z2, z3, z4) = choose b4 (x0, x1, x2, x3, x4) (t0, t1, t2, t3, t4) in
  assert (
    if as_nat5 (x0, x1, x2, x3, x4) >= S.q
    then as_nat5 (z0, z1, z2, z3, z4) == as_nat5 (t0, t1, t2, t3, t4)
    else as_nat5 (z0, z1, z2, z3, z4) == as_nat5 (x0, x1, x2, x3, x4));
  assert (
    if as_nat5 (x0, x1, x2, x3, x4) >= S.q
    then v b4 == 0 /\ as_nat5 (z0, z1, z2, z3, z4) == as_nat5 (t0, t1, t2, t3, t4)
    else v b4 == 1 /\ as_nat5 (z0, z1, z2, z3, z4) == as_nat5 (x0, x1, x2, x3, x4));
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val carry56: x:uint64 ->
  Pure (uint64 & uint64)
  (requires v x <= pow2 57)
  (ensures  fun (t, c) ->
    v t < pow56 /\ v c <= 2 /\
    v x == v c * pow56 + v t)

let carry56 x =
  let carry = x >>. 56ul in
  FStar.Math.Lemmas.pow2_minus 57 56;
  let t     = x &. mask56 in
  assert_norm (pow2 56 < pow2 64);
  mod_mask_lemma x 56ul;
  assert (v (mod_mask #U64 #SEC 56ul) == v mask56);
  assert (v t == v x % pow2 56);
  assert (v x == v carry * pow2 56 + v t);
  t, carry


inline_for_extraction noextract
val add_modq5:
    x:qelem5
  -> y:qelem5
  -> Pure qelem5
    (requires
      qelem_fits5 x (1, 1, 1, 1, 1) /\
      qelem_fits5 y (1, 1, 1, 1, 1) /\
      as_nat5 x < S.q /\ as_nat5 y < S.q)
    (ensures fun z ->
      qelem_fits5 z (1, 1, 1, 1, 1) /\
      as_nat5 z == (as_nat5 x + as_nat5 y) % S.q)

let add_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  assert_norm (pow56 - 1 + pow56 - 1 == pow2 57 - 2);
  let (t0, c0) = carry56 (x0 +! y0) in
  let (t1, c1) = carry56 (x1 +! y1 +! c0) in
  let (t2, c2) = carry56 (x2 +! y2 +! c1) in
  let (t3, c3) = carry56 (x3 +! y3 +! c2) in
  let t4 = x4 +! y4 +! c3 in
  assert (as_nat5 (t0, t1, t2, t3, t4) == as_nat5 (x0, x1, x2, x3, x4) + as_nat5 (y0, y1, y2, y3, y4));
  let (o0, o1, o2, o3, o4) = subm_conditional (t0, t1, t2, t3, t4) in
  Lemmas.lemma_add_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) (t0, t1, t2, t3, t4);
  (o0, o1, o2, o3, o4)


inline_for_extraction noextract
val carry56_wide: x:uint128 ->
  Pure (uint128 & uint64)
  (requires v x < pow2 117)
  (ensures fun (c, t) -> v t < pow56 /\ v c < pow2 61 /\
    v x - v c * pow56 == v t /\
    v c == v x / pow56)

let carry56_wide x =
  let carry = x >>. 56ul in
  let t     = to_u64 x &. mask56 in
  assert_norm (pow2 56 < pow2 64);
  Math.Lemmas.lemma_div_lt_nat (v x) 117 56;
  mod_mask_lemma (to_u64 x) 56ul;
  assert (v (mod_mask #U64 #SEC 56ul) == v mask56);
  assert (v t == (v x % pow2 64) % pow2 56);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v x) 56 64;
  assert (v t == v x % pow2 56);
  assert (v x == v carry * pow2 56 + v t);
  carry, t

inline_for_extraction noextract
val mul64_wide_5:
  (a:uint64) -> (b:uint64) ->
  Pure uint128
  (requires qelem_fits1 a 1 /\ qelem_fits1 b 1)
  (ensures fun z ->
    v z == v a * v b /\
    v z <= pow2 112 - pow2 57 + 1 /\
    v z < pow2 112)
let mul64_wide_5 a b =
  let lemma_smaller (a b:uint64) : Lemma
    (requires qelem_fits1 a 1 /\ qelem_fits1 b 1)
    (ensures v (mul64_wide a b) < pow2 112)
    = if v a = 0 || v b = 0 then () else
      calc (<) {
       v a * v b <: int;
       (<) { Math.Lemmas.lemma_mult_lt_left (v a) (v b) (pow2 56) }
       v a * pow2 56;
       (<) { Math.Lemmas.lemma_mult_lt_right (pow2 56) (v a) (pow2 56) }
       pow2 56 * pow2 56;
       (==) { assert_norm (pow2 56 * pow2 56 == pow2 112) }
       pow2 112;
      }
  in
  let lemma_le (a b:uint64) : Lemma
    (requires qelem_fits1 a 1 /\ qelem_fits1 b 1)
    (ensures v (mul64_wide a b) <= pow2 112 - pow2 57 + 1)
    = if v a = 0 || v b = 0 then () else
      assert_norm (pow2 112 - pow2 57 + 1 >= 0);
      calc (<=) {
       v a * v b <: int;
       (<=) { Math.Lemmas.lemma_mult_le_left (v a) (v b) (pow2 56 - 1) }
       v a * (pow2 56 - 1);
       (<=) { Math.Lemmas.lemma_mult_le_right (pow2 56 - 1) (v a) (pow2 56 - 1) }
       (pow2 56 - 1) * (pow2 56 - 1);
       (==) { assert_norm ((pow2 56 - 1) * (pow2 56 - 1) == pow2 112 - pow2 57 + 1) }
       pow2 112 - pow2 57 + 1;
      }
  in
  lemma_le a b;
  lemma_smaller a b;
  mul64_wide a b

inline_for_extraction noextract
val add2:
  (a:uint128) -> (b:uint128) ->
  Pure uint128
  (requires v a < pow2 112 /\ v b < pow2 112)
  (ensures fun z ->
    v z == v a + v b /\
    v z <= pow2 116)
let add2 a b =
  assert_norm (pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 <= pow2 116);
  Math.Lemmas.small_mod (v a + v b) (pow2 128);
  a +. b

inline_for_extraction noextract
val add3:
  (a:uint128) -> (b:uint128) -> (c:uint128) ->
  Pure uint128
  (requires v a < pow2 112 /\ v b < pow2 112 /\ v c < pow2 112 )
  (ensures fun z ->
    v z == v a + v b + v c /\
    v z <= pow2 116)
let add3 a b c =
  assert_norm (pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 <= pow2 116);
  Math.Lemmas.small_mod (v a + v b) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c) (pow2 128);
  a +. b +. c

inline_for_extraction noextract
val add4:
  (a:uint128) -> (b:uint128) -> (c:uint128) -> (d:uint128) ->
  Pure uint128
  (requires v a < pow2 112 /\ v b < pow2 112 /\ v c < pow2 112 /\ v d < pow2 112)
  (ensures fun z ->
    v z == v a + v b + v c + v d /\
    v z <= pow2 116)
let add4 a b c d =
  assert_norm (pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 + pow2 112 <= pow2 116);
  Math.Lemmas.small_mod (v a + v b) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c + v d) (pow2 128);
  a +. b +. c +. d

inline_for_extraction noextract
val add5:
  (a:uint128) -> (b:uint128) -> (c:uint128) -> (d:uint128) -> (e:uint128) ->
  Pure uint128
  (requires v a < pow2 112 /\ v b < pow2 112 /\ v c < pow2 112 /\ v d < pow2 112 /\ v e < pow2 112)
  (ensures fun z ->
    v z == v a + v b + v c + v d + v e/\
    v z <= pow2 116)
let add5 a b c d e =
  assert_norm (pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 + pow2 112 + pow2 112 < pow2 128);
  assert_norm (pow2 112 + pow2 112 + pow2 112 + pow2 112 + pow2 112 <= pow2 116);
  Math.Lemmas.small_mod (v a + v b) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c + v d) (pow2 128);
  Math.Lemmas.small_mod (v a + v b + v c + v d + v e) (pow2 128);
  a +. b +. c +. d +. e

inline_for_extraction noextract
val add_inner_carry:
  (a:uint128) -> (b:uint128) ->
  Pure uint128
  (requires v a <= pow2 116 /\ v b < pow2 61)
  (ensures fun z ->
    v z == v a + v b /\
    v z < pow2 117)
let add_inner_carry a b =
  assert_norm (pow2 116 + pow2 61 < pow2 128);
  assert_norm (pow2 116 + pow2 61 < pow2 117);
  Math.Lemmas.small_mod (v a + v b) (pow2 128);
  a +. b

inline_for_extraction noextract
val mul_5:
    x:qelem5
  -> y:qelem5 ->
  Pure qelem_wide5
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    qelem_fits5 y (1, 1, 1, 1, 1))
  (ensures fun r ->
    qelem_wide_fits5 r (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 r == as_nat5 x * as_nat5 y)

let lemma_mult_distr_3 (a b c:nat) (n:nat) : Lemma
  ((a + b - c * pow2 56) * pow2 n == a * pow2 n + b * pow2 n - c * pow2 (n + 56))
  =
    Math.Lemmas.distributivity_sub_left (a + b) (c * pow2 56) (pow2 n);
    Math.Lemmas.distributivity_add_left a b (pow2 n);
    Math.Lemmas.pow2_plus 56 n


#set-options "--z3rlimit 200"

let mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let xy00 = mul64_wide_5 x0 y0 in
  let xy01 = mul64_wide_5 x0 y1 in
  let xy02 = mul64_wide_5 x0 y2 in
  let xy03 = mul64_wide_5 x0 y3 in
  let xy04 = mul64_wide_5 x0 y4 in
  let xy10 = mul64_wide_5 x1 y0 in
  let xy11 = mul64_wide_5 x1 y1 in
  let xy12 = mul64_wide_5 x1 y2 in
  let xy13 = mul64_wide_5 x1 y3 in
  let xy14 = mul64_wide_5 x1 y4 in
  let xy20 = mul64_wide_5 x2 y0 in
  let xy21 = mul64_wide_5 x2 y1 in
  let xy22 = mul64_wide_5 x2 y2 in
  let xy23 = mul64_wide_5 x2 y3 in
  let xy24 = mul64_wide_5 x2 y4 in
  let xy30 = mul64_wide_5 x3 y0 in
  let xy31 = mul64_wide_5 x3 y1 in
  let xy32 = mul64_wide_5 x3 y2 in
  let xy33 = mul64_wide_5 x3 y3 in
  let xy34 = mul64_wide_5 x3 y4 in
  let xy40 = mul64_wide_5 x4 y0 in
  let xy41 = mul64_wide_5 x4 y1 in
  let xy42 = mul64_wide_5 x4 y2 in
  let xy43 = mul64_wide_5 x4 y3 in
  let xy44 = mul64_wide_5 x4 y4 in
  let z0 = xy00 in // < pow2 112
  let z1 = add2 xy01 xy10 in // < pow2 113
  let z2 = add3 xy02 xy11 xy20 in // < pow2 114
  let z3 = add4 xy03 xy12 xy21 xy30 in // < pow2 115
  let z4 = add5 xy04 xy13 xy22 xy31 xy40 in // < pow2 116
  let z5 = add4      xy14 xy23 xy32 xy41 in
  let z6 = add3           xy24 xy33 xy42 in
  let z7 = add2                xy34 xy43 in
  let z8 =                          xy44 in
  //(z0, z1, z2, z3, z4, z5, z6, z7, z8)


  assert_norm (pow2 112 < pow2 117);
  assert_norm (pow2 112 <= pow2 116);
  let (c0, t0) = carry56_wide z0 in
  let (c1, t1) = carry56_wide (add_inner_carry z1 c0) in
  let (c2, t2) = carry56_wide (add_inner_carry z2 c1) in
  let (c3, t3) = carry56_wide (add_inner_carry z3 c2) in
  let (c4, t4) = carry56_wide (add_inner_carry z4 c3) in
  let (c5, t5) = carry56_wide (add_inner_carry z5 c4) in
  let (c6, t6) = carry56_wide (add_inner_carry z6 c5) in
  let (c7, t7) = carry56_wide (add_inner_carry z7 c6) in
  let (c8, t8) = carry56_wide (add_inner_carry z8 c7) in
  let t9 = to_u64 c8 in
  let lemma_t9_fits () : Lemma (v t9 < pow2 56)
    = // This proof was built from the bottom. We have as a constraint that v c8 has to be < pow2 112 to satisfy the postcondition.
      // We compute each time the maximal value such that this postcondition is satisfied

      calc (<) {
        v c0;
        (<) { Math.Lemmas.lemma_div_lt_nat (v z0) 112 56 }
        pow2 56;
      };
      calc (<) {
        v c1;
        (<) { assert_norm (2*(pow2 112 - pow2 57 + 1) + pow2 56 <= pow2 113);
          Math.Lemmas.lemma_div_lt_nat (v z1 + v c0) 113 56 }
        pow2 57;
      };
      calc (<) {
        v c2;
        (<) { assert_norm (3*(pow2 112 - pow2 57 + 1) + pow2 57 <= pow2 114);
          Math.Lemmas.lemma_div_lt_nat (v z2 + v c1) 114 56 }
        pow2 58;
      };
      calc (<=) {
        v c3;
        (<=) { assert_norm (4*(pow2 112 - pow2 57 + 1) + pow2 58 <= 31153781151208965410895007785680895);
           assert_norm (31153781151208965410895007785680895 / pow56 == 432345564227567610);
          Math.Lemmas.lemma_div_le (v z3 + v c2) 31153781151208965410895007785680895 (pow2 56) }
        432345564227567610;
      };
      calc (<=) {
        v c4;
        (<=) { assert_norm (5*(pow2 112 - pow2 57 + 1) + 432345564227567610 <= 25961484292674137854422105494388735); // (pow2 59 - 2) * pow56
          assert_norm (25961484292674137854422105494388735 / pow56 == 360287970189639675);
          Math.Lemmas.lemma_div_le (v z4 + v c3) 25961484292674137854422105494388735 (pow2 56) }
        360287970189639675;
      };
      calc (<=) {
        v c5;
        (<=) { assert_norm (4*(pow2 112 - pow2 57 + 1) + 360287970189639675 <= 20769187434139310297949203203096575);
          Math.Lemmas.lemma_div_le (v z5 + v c4) 20769187434139310297949203203096575 (pow2 56);
          assert_norm (20769187434139310297949203203096575 / pow2 56 == pow2 58 - 4) }
        pow2 58 - 4;
      };

      calc (<=) {
        v c6;
        (<=) { assert_norm (3*(pow2 112 - pow2 57 + 1) + pow2 58 - 4 <= 15576890575604482741476300911804415);
          Math.Lemmas.lemma_div_le (v z6 + v c5) 15576890575604482741476300911804415 (pow2 56);
          assert_norm (15576890575604482741476300911804415 / pow2 56 == 216172782113783805) }
        216172782113783805;
      };
      calc (<=) {
        v c7;
        (<=) { assert_norm (2*(pow2 112 - pow2 57 + 1) + 216172782113783805 <= 10384593717069655185003398620512255); // (pow2 57 - 1) * pow2 56 - 1
          Math.Lemmas.lemma_div_le (v z7 + v c6) 10384593717069655185003398620512255 (pow2 56);
          assert_norm (10384593717069655185003398620512255 / pow2 56 == pow2 57 - 2) }
        pow2 57 - 2;
      };
      calc (<) {
        v c8;
        (<) { Math.Lemmas.lemma_div_lt_nat (v z8 + v c7) 112 56 }
        pow2 56;
      };
      assert_norm (pow2 56 < pow2 64);
      Math.Lemmas.small_mod (v c8) (pow2 64)
  in

  lemma_t9_fits();

  calc (==) {
    wide_as_nat5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) <: int;
    (==) { }
    v t0 + v t1 * pow56 + v t2 * pow112 + v t3 * pow168 + v t4 * pow224 +
    v t5 * pow280 + v t6 * pow336 + v t7 * pow392 + v t8 * pow448 + v t9 * pow504;
    (==) { assert_norm (pow2 61 < pow2 64);
           Math.Lemmas.small_mod (v c8) (pow2 64)
    }
    v z0 - v c0 * pow2 56 +
    (v z1 + v c0 - v c1 * pow2 56) * pow56 +
    (v z2 + v c1 - v c2 * pow2 56) * pow112 +
    (v z3 + v c2 - v c3 * pow2 56) * pow168 +
    (v z4 + v c3 - v c4 * pow2 56) * pow224 +
    (v z5 + v c4 - v c5 * pow2 56) * pow280 +
    (v z6 + v c5 - v c6 * pow2 56) * pow336 +
    (v z7 + v c6 - v c7 * pow2 56) * pow392 +
    (v z8 + v c7 - v c8 * pow2 56) * pow448 +
    v c8 * pow504;
    (==) {
      lemma_mult_distr_3 (v z1) (v c0) (v c1) 56;
      lemma_mult_distr_3 (v z2) (v c1) (v c2) 112;
      lemma_mult_distr_3 (v z3) (v c2) (v c3) 168;
      lemma_mult_distr_3 (v z4) (v c3) (v c4) 224;
      lemma_mult_distr_3 (v z5) (v c4) (v c5) 280;
      lemma_mult_distr_3 (v z6) (v c5) (v c6) 336;
      lemma_mult_distr_3 (v z7) (v c6) (v c7) 392;
      lemma_mult_distr_3 (v z8) (v c7) (v c8) 448
    }
    v z0 +
    v z1 * pow56 +
    v z2 * pow112 +
    v z3 * pow168 +
    v z4 * pow224 +
    v z5 * pow280 +
    v z6 * pow336 +
    v z7 * pow392 +
    v z8 * pow448;
    (==) { calc (==) {
             v z1;
             (==) { }
             v x0 * v y1 + v x1 * v y0;
           };
           calc (==) {
             v z2;
             (==) { }
             v x0 * v y2 + v x1 * v y1 + v x2 * v y0;
           };
           calc (==) {
             v z3;
             (==) { }
             v x0 * v y3 + v x1 * v y2 + v x2 * v y1 + v x3 * v y0;
           };
           calc (==) {
             v z4;
             (==) { }
             v x0 * v y4 + v x1 * v y3 + v x2 * v y2 + v x3 * v y1 + v x4 * v y0;
           };
           calc (==) {
             v z5;
             (==) { }
             v x1 * v y4 + v x2 * v y3 + v x3 * v y2 + v x4 * v y1;
           };
           calc (==) {
             v z6;
             (==) { }
             v x2 * v y4 + v x3 * v y3 + v x4 * v y2;
           };
           calc (==) {
             v z7;
             (==) { }
             v x3 * v y4 + v x4 * v y3;
           };
           calc (==) {
             v z8;
             (==) { }
             v x4 * v y4;
           }
         }
    v x0 * v y0 +
    (v x0 * v y1 + v x1 * v y0) * pow56 +
    (v x0 * v y2 + v x1 * v y1 + v x2 * v y0) * pow112 +
    (v x0 * v y3 + v x1 * v y2 + v x2 * v y1 + v x3 * v y0) * pow168 +
    (v x0 * v y4 + v x1 * v y3 + v x2 * v y2 + v x3 * v y1 + v x4 * v y0) * pow224 +
    (v x1 * v y4 + v x2 * v y3 + v x3 * v y2 + v x4 * v y1) * pow280 +
    (v x2 * v y4 + v x3 * v y3 + v x4 * v y2) * pow336 +
    (v x3 * v y4 + v x4 * v y3) * pow392 +
    (v x4 * v y4) * pow448;
    (==) { Lemmas.lemma_mul_qelem5 (v x0) (v x1) (v x2) (v x3) (v x4) (v y0) (v y1) (v y2) (v y3) (v y4) }
    (v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168 + v x4 * pow2 224) *
    (v y0 + v y1 * pow2 56 + v y2 * pow2 112 + v y3 * pow2 168 + v y4 * pow2 224);
  };

  (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9)

inline_for_extraction noextract
val low_mul_5:
    x:qelem5
  -> y:qelem5 ->
  Pure qelem5
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    qelem_fits5 y (1, 1, 1, 1, 1))
  (ensures fun r ->
    qelem_fits5 r (1, 1, 1, 1, 1) /\
    as_nat5 r == (as_nat5 x * as_nat5 y) % pow2 264)

let low_mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let xy00 = mul64_wide_5 x0 y0 in
  let xy01 = mul64_wide_5 x0 y1 in
  let xy02 = mul64_wide_5 x0 y2 in
  let xy03 = mul64_wide_5 x0 y3 in
  let xy04 = mul64_wide_5 x0 y4 in
  let xy10 = mul64_wide_5 x1 y0 in
  let xy11 = mul64_wide_5 x1 y1 in
  let xy12 = mul64_wide_5 x1 y2 in
  let xy13 = mul64_wide_5 x1 y3 in
  let xy20 = mul64_wide_5 x2 y0 in
  let xy21 = mul64_wide_5 x2 y1 in
  let xy22 = mul64_wide_5 x2 y2 in
  let xy30 = mul64_wide_5 x3 y0 in
  let xy31 = mul64_wide_5 x3 y1 in
  let xy40 = mul64_wide_5 x4 y0 in

  assert_norm (pow2 112 < pow2 117);
  let (c0, t0) = carry56_wide xy00 in
  let (c1, t1) = carry56_wide (add_inner_carry (add2 xy01 xy10) c0) in
  let (c2, t2) = carry56_wide (add_inner_carry (add3 xy02 xy11 xy20) c1) in
  let (c3, t3) = carry56_wide (add_inner_carry (add4 xy03 xy12 xy21 xy30)  c2) in
  let t4 = to_u64 (add_inner_carry (add5 xy04 xy13 xy22 xy31 xy40) c3) &. mask40 in

  calc (==) {
    as_nat5 (t0, t1, t2, t3, t4) <: int;
    (==) { }
    v t0 + v t1 * pow56 + v t2 * pow112 + v t3 * pow168 + v t4 * pow224;
    (==) { }
    v xy00 - v c0 * pow2 56 +
    (v xy01 + v xy10 + v c0 - v c1 * pow2 56) * pow56 +
    (v xy02 + v xy11 + v xy20 + v c1 - v c2 * pow56) * pow112 +
    (v xy03 + v xy12 + v xy21 + v xy30 + v c2 - v c3 * pow56) * pow168 +
    v t4 * pow224;
    (==) { logand_mask (to_u64 (add_inner_carry (add5 xy04 xy13 xy22 xy31 xy40) c3)) mask40 40;
      Math.Lemmas.pow2_modulo_modulo_lemma_1 (v (add_inner_carry (add5 xy04 xy13 xy22 xy31 xy40) c3)) 40 64
    }
    v x0 * v y0 +
    (v x0 * v y1 + v x1 * v y0) * pow56 +
    (v x0 * v y2 + v x1 * v y1 + v x2 * v y0) * pow112 +
    (v x0 * v y3 + v x1 * v y2 + v x2 * v y1 + v x3 * v y0  - v c3 * pow56) * pow168 +
    ((v x0 * v y4 + v x1 * v y3 + v x2 * v y2 + v x3 * v y1 + v x4 * v y0 + v c3) % pow2 40) * pow224;
  };

  Lemmas.lemma_mul_5_low_264 (v x0) (v x1) (v x2) (v x3) (v x4) (v y0) (v y1) (v y2) (v y3) (v y4);

  (t0, t1, t2, t3, t4)


inline_for_extraction noextract
val div_2_24_step: x:uint64 -> y:uint64 ->
  Pure uint64
  (requires v x < pow56 /\ v y < pow56)
  (ensures  fun r -> v r < pow56 /\
    v r == v x / pow2 24 + pow2 32 * (v y % pow2 24))

let div_2_24_step x y =
  let y' = (y &. u64 0xffffff) <<. 32ul in
  assert_norm (pow2 24 - 1 = 0xffffff);
  assert_norm (pow2 24 < pow2 64);
  mod_mask_lemma y 24ul;
  assert (v (mod_mask #U64 #SEC 24ul) == 0xffffff);
  assert (v (y &. u64 0xffffff) == v y % pow2 24);
  assert (v y' == (v y % pow2 24) * pow2 32);
  let x' = x >>. 24ul in
  FStar.Math.Lemmas.pow2_minus 56 24;
  assert (v x' < pow2 32);
  let z = x' |. y' in
  logor_disjoint x' y' 32;
  assert (v z == v x / pow2 24 + pow2 32 * (v y % pow2 24));
  z


inline_for_extraction noextract
val div_248: x:qelem_wide5 ->
  Pure qelem5
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 512)
  (ensures fun r ->
    qelem_fits5 r (1, 1, 1, 1, 1) /\
    as_nat5 r == (wide_as_nat5 x) / pow2 248)

let div_248 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) =
  // x / pow2 248 == (x / pow2 224) / pow2 24
  let z0 = div_2_24_step x4 x5 in
  let z1 = div_2_24_step x5 x6 in
  let z2 = div_2_24_step x6 x7 in
  let z3 = div_2_24_step x7 x8 in
  let z4 = div_2_24_step x8 x9 in
  assert (qelem_fits5 (z0, z1, z2, z3, z4) (1, 1, 1, 1, 1));
  Lemmas.lemma_div248 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9);
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val div_2_40_step: x:uint64 -> y:uint64 ->
  Pure uint64
  (requires v x < pow56)
  (ensures  fun z -> v z < pow56 /\
    v z == v x / pow2 40 + pow2 16 * (v y % pow2 40))

let div_2_40_step x y =
  let y' = (y &. mask40) <<. 16ul in
  assert_norm (pow2 40 < pow2 64);
  mod_mask_lemma y 40ul;
  assert (v (mod_mask #U64 #SEC 40ul) == v mask40);
  assert (v y' == (v y % pow2 40) * pow2 16);

  let x' = x >>. 40ul in
  FStar.Math.Lemmas.pow2_minus 56 40;
  assert (v x' == v x / pow2 40);
  assert (v x' < pow2 16);
  let z = x' |. y' in
  logor_disjoint x' y' 16;
  z


inline_for_extraction noextract
val div_264: x:qelem_wide5 ->
  Pure qelem5
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 528)
  (ensures fun z ->
    qelem_fits5 z (1, 1, 1, 1, 1) /\
    as_nat5 z == (wide_as_nat5 x) / pow2 264)

let div_264 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) =
  // x / pow2 264 == (x / pow2 224) / pow2 40
  let z0 = div_2_40_step x4 x5 in
  let z1 = div_2_40_step x5 x6 in
  let z2 = div_2_40_step x6 x7 in
  let z3 = div_2_40_step x7 x8 in
  let z4 = div_2_40_step x8 x9 in
  assert (qelem_fits5 (z0, z1, z2, z3, z4) (1, 1, 1, 1, 1));
  Lemmas.lemma_div264 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9);
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val mod_264: t:qelem_wide5 ->
  Pure qelem5
  (requires
    qelem_wide_fits5 t (1, 1, 1, 1, 1, 1, 1, 1, 1, 1))
  (ensures fun r ->
    qelem_fits5 r (1, 1, 1, 1, 1) /\
    as_nat5 r == (wide_as_nat5 t) % pow2 264)

let mod_264 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) =
  Lemmas.lemma_mod_264 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9);
  (t0, t1, t2, t3, t4 &. mask40)


inline_for_extraction noextract
val subm_last_step: x:uint64 -> y:uint64 ->
  Pure (uint64 & uint64)
  (requires v x < pow2 40 /\ v y <= pow2 40)
  (ensures  fun (b, t) -> v b <= 1 /\ v t < pow2 40 /\
    v x - v y == v t - pow2 40 * v b)

let subm_last_step x y =
  assert_norm (pow2 40 < pow2 63);
  let b = (x -. y) >>. 63ul in
  assert (if v x >= v y then v b == 0 else v b == 1);
  let t = ((b <<. 40ul) +! x) -! y in
  b, t

#push-options "--z3rlimit 400 --max_fuel 0 --max_ifuel 0"
inline_for_extraction noextract
val sub_mod_264: x:qelem5 -> y:qelem5 ->
  Pure qelem5
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    qelem_fits5 y (1, 1, 1, 1, 1) /\
    as_nat5 x < pow2 264 /\
    as_nat5 y < pow2 264)
  (ensures fun z ->
    qelem_fits5 z (1, 1, 1, 1, 1) /\
   (if as_nat5 x >= as_nat5 y then
      as_nat5 z == as_nat5 x - as_nat5 y
    else
      as_nat5 z == as_nat5 x - as_nat5 y + pow2 264))

let sub_mod_264 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (c1, t0) = subm_step x0 y0 in
  assert (v x0 - v y0 == v t0 - v c1 * pow56);
  let (c2, t1) = subm_step x1 (y1 +! c1) in
  assert (v x1 - v y1 - v c1 == v t1 - v c2 * pow56);
  let (c3, t2) = subm_step x2 (y2 +! c2) in
  assert (v x2 - v y2 - v c2 == v t2 - v c3 * pow56);
  let (c4, t3) = subm_step x3 (y3 +! c3) in
  assert (v x3 - v y3 - v c3 == v t3 - v c4 * pow56);
  Lemmas.lemma_as_nat_pow264_x4 (x0, x1, x2, x3, x4);
  Lemmas.lemma_as_nat_pow264_x4 (y0, y1, y2, y3, y4);
  let (c5, t4) = subm_last_step x4 (y4 +! c4) in
  assert (v x4 - v y4 - v c4 == v t4 - pow2 40 * v c5);
  assert (
    if v c5 = 0 then as_nat5 (x0, x1, x2, x3, x4) >= as_nat5 (y0, y1, y2, y3, y4)
    else as_nat5 (x0, x1, x2, x3, x4) < as_nat5 (y0, y1, y2, y3, y4));

  assert_norm (pow2 40 < pow2 56);
  assert (qelem_fits5 (t0, t1, t2, t3, t4) (1, 1, 1, 1, 1));
  assert
   (as_nat5 (t0, t1, t2, t3, t4) ==
    v x0 - v y0 + v c1 * pow56 +
    (v x1 - v y1 - v c1 + v c2 * pow56) * pow56 +
    (v x2 - v y2 - v c2 + v c3 * pow56) * pow112 +
    (v x3 - v y3 - v c3 + v c4 * pow56) * pow168 +
    (v x4 - v y4 - v c4 + pow2 40 * v c5) * pow224);
  Lemmas.lemma_sub_mod_264_aux (v x0) (v x1) (v x2) (v x3) (v x4)
    (v y0) (v y1) (v y2) (v y3) (v y4) (v c1) (v c2) (v c3) (v c4) (v c5);

  assert (as_nat5 (t0, t1, t2, t3, t4) ==
    as_nat5 (x0, x1, x2, x3, x4) - as_nat5 (y0, y1, y2, y3, y4) + v c5 * pow2 264);
  Lemmas.lemma_sub_mod_264 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) (t0, t1, t2, t3, t4) c5;
  (t0, t1, t2, t3, t4)
#pop-options


// A = t, L = make_m()
// b = 2^8, k = 32, mu = b^{2*k} / L = make_mu()
inline_for_extraction noextract
val barrett_reduction5: t:qelem_wide5 ->
  Pure qelem5
  (requires
    qelem_wide_fits5 t (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 t < pow2 512)
  (ensures  fun z ->
    qelem_fits5 z (1, 1, 1, 1, 1) /\
    as_nat5 z == (wide_as_nat5 t) % S.q)

let barrett_reduction5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) =
  let (m0, m1, m2, m3, m4) = make_m () in
  let (mu0, mu1, mu2, mu3, mu4) = make_mu () in

  let (q0, q1, q2, q3, q4) = div_248 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) in
  assert (as_nat5 (q0, q1, q2, q3, q4) == wide_as_nat5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) / pow2 248);
  FStar.Math.Lemmas.lemma_div_lt_nat (wide_as_nat5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9)) 512 248;
  assert (as_nat5 (q0, q1, q2, q3, q4) < pow2 264);

  let (qmu0', qmu1', qmu2', qmu3', qmu4', qmu5', qmu6', qmu7', qmu8', qmu9') = mul_5 (q0, q1, q2, q3, q4) (mu0, mu1, mu2, mu3, mu4) in
  FStar.Math.Lemmas.lemma_mult_lt_right (pow2 512 / S.q) (as_nat5 (q0, q1, q2, q3, q4)) (pow2 264);
  assert (wide_as_nat5 (qmu0', qmu1', qmu2', qmu3', qmu4', qmu5', qmu6', qmu7', qmu8', qmu9') <= pow2 512 / S.q * pow2 264);
  assert_norm (pow2 512 / S.q * pow2 264 < pow2 528);

  let (qdiv0, qdiv1, qdiv2, qdiv3, qdiv4) = div_264 (qmu0', qmu1', qmu2', qmu3', qmu4', qmu5', qmu6', qmu7', qmu8', qmu9') in
  //u = qdiv == (A / b^{k-1}) * mu / b^{k+1} == ((A / 2^248) * mu) / 2^264

  let (r0, r1, r2, r3, r4) = mod_264 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) in
  //r == A mod b^{k+1} == A mod 2^264

  let (qmul0, qmul1, qmul2, qmul3, qmul4) = low_mul_5 (qdiv0, qdiv1, qdiv2, qdiv3, qdiv4) (m0, m1, m2, m3, m4) in
  //v == qmul == u * L mod b^{k+1} == u * L mod 2^264

  let (s0, s1, s2, s3, s4) = sub_mod_264 (r0, r1, r2, r3, r4) (qmul0, qmul1, qmul2, qmul3, qmul4) in
  //u == s == (r - v) mod b^{k+1} == (r - v) mod 2^264

  let (o0, o1, o2, o3, o4) = subm_conditional (s0, s1, s2, s3, s4) in
  Lemmas.lemma_barrett_reduce' (wide_as_nat5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9));

  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val mul_modq5: x:qelem5 -> y:qelem5 ->
  Pure qelem5
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    qelem_fits5 y (1, 1, 1, 1, 1) /\
    as_nat5 x < pow2 256 /\
    as_nat5 y < pow2 256)
  (ensures  fun r ->
    qelem_fits5 r (1, 1, 1, 1, 1) /\
    as_nat5 r == (as_nat5 x * as_nat5 y) % S.q)

let mul_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) = mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) in
  Lemmas.lemma_mul_lt (as_nat5 (x0, x1, x2, x3, x4)) (pow2 256) (as_nat5 (y0, y1, y2, y3, y4)) (pow2 256);
  assert_norm (pow2 256 * pow2 256 = pow2 512);
  let (o0, o1, o2, o3, o4) = barrett_reduction5 (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) in
  (o0, o1, o2, o3, o4)
