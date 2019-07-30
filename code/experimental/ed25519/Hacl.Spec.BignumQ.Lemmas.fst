module Hacl.Spec.BignumQ.Lemmas

open FStar.Mul
open Lib.IntTypes

module S = Spec.Ed25519

include Hacl.Spec.BignumQ.Definitions


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val lemma_mul_lt:a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma
  (requires a < b /\ c < d)
  (ensures  a * c < b * d)

let lemma_mul_lt a b c d = ()


val lemma_as_nat5: f:qelem5 ->
  Lemma
  (requires qelem_fits5 f (1, 1, 1, 1, 1))
  (ensures  as_nat5 f < pow2 280)

let lemma_as_nat5 f =
  //let (f0, f1, f2, f3, f4) = f in
  //assert (as_nat5 f == v f0 + v f1 * pow56 + v f2 * pow112 + v f3 * pow168 + v f4 * pow224);
  assert_norm (pow2 56 * pow2 56 = pow2 112);
  assert_norm (pow2 56 * pow2 112 = pow2 168);
  assert_norm (pow2 56 * pow2 168 = pow2 224);
  assert_norm (pow2 56 * pow2 224 = pow2 280)


val lemma_choose_step:
    bit:uint64{v bit <= 1}
  -> x:uint64
  -> y:uint64
  -> Lemma
     (let mask = bit -. u64 1 in
      let z = x ^. (mask &. (x ^. y)) in
      if v bit = 1 then z == x else z == y)

let lemma_choose_step bit p1 p2 =
  let mask = bit -. u64 1 in
  assert (v bit == 0 ==> v mask == pow2 64 - 1);
  assert (v bit == 1 ==> v mask == 0);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == 0);
  assert (v bit == 0 ==> v dummy ==  v (p1 ^. p2));
  let p1' = p1 ^. dummy in
  assert (v dummy == v (if v bit = 1 then u64 0 else (p1 ^. p2)));
  logxor_lemma p1 p2


val lemma_subm_conditional:
    x0:nat -> x1:nat -> x2:nat -> x3:nat -> x4:nat
  -> y0:nat -> y1:nat -> y2:nat -> y3:nat -> y4:nat
  -> b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  Lemma (
    x0 - y0 + b0 * pow2 56 +
    (x1 - y1 - b0 + b1 * pow2 56) * pow2 56 +
    (x2 - y2 - b1 + b2 * pow2 56) * pow2 112 +
    (x3 - y3 - b2 + b3 * pow2 56) * pow2 168 +
    (x4 - y4 - b3 + b4 * pow2 56) * pow2 224 ==
    (x0 + x1 * pow2 56 + x2 * pow2 112 + x3 * pow2 168 + x4 * pow2 224) -
    (y0 + y1 * pow2 56 + y2 * pow2 112 + y3 * pow2 168 + y4 * pow2 224) + b4 * pow2 280)

let lemma_subm_conditional x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 b0 b1 b2 b3 b4 =
  assert_norm (pow2 56 * pow2 56 = pow2 112);
  assert_norm (pow2 56 * pow2 112 = pow2 168);
  assert_norm (pow2 56 * pow2 168 = pow2 224);
  assert_norm (pow2 56 * pow2 224 = pow2 280)


val lemma_div224: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1))
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    wide_as_nat5 x / pow2 224 ==
    v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280))

let lemma_div224 x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  assert
    (wide_as_nat5 x ==
     v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168 + v x4 * pow2 224 +
     v x5 * pow2 280 + v x6 * pow2 336 + v x7 * pow2 392 + v x8 * pow2 448 + v x9 * pow2 504);
  assert_norm (pow2 56 * pow2 224 == pow2 280);
  assert_norm (pow2 112 * pow2 224 == pow2 336);
  assert_norm (pow2 168 * pow2 224 == pow2 392);
  assert_norm (pow2 224 * pow2 224 == pow2 448);
  assert_norm (pow2 280 * pow2 224 == pow2 504);
  let open FStar.Calc in
  calc (==) {
    wide_as_nat5 x / pow2 224;
    (==) { }
    (v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168 +
    (v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280) * pow2 224) / pow2 224;
    (==) {
      FStar.Math.Lemmas.lemma_div_plus
	(v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168)
	(v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280) (pow2 224) }
    (v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168) / pow2 224 +
    v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280;
    (==) { FStar.Math.Lemmas.small_division_lemma_1 (v x0 + v x1 * pow2 56 + v x2 * pow2 112 + v x3 * pow2 168) (pow2 224) }
      v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280;
    }


#set-options "--z3rlimit 200"

val lemma_div248_aux: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 512)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    wide_as_nat5 x / pow2 248 ==
      v x4 / pow2 24 + v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 + v x9 * pow2 256))

let lemma_div248_aux x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  assert_norm (pow2 248 == pow2 224 * pow2 24);
  assert_norm (pow2 56 == pow2 32 * pow2 24);
  assert_norm (pow2 112 == pow2 88 * pow2 24);
  assert_norm (pow2 168 == pow2 144 * pow2 24);
  assert_norm (pow2 224 == pow2 200 * pow2 24);
  assert_norm (pow2 280 == pow2 256 * pow2 24);
  assert_norm (0 < pow2 24);

  calc (==) {
    wide_as_nat5 x / pow2 248;
  (==) { FStar.Math.Lemmas.division_multiplication_lemma (wide_as_nat5 x) (pow2 224) (pow2 24) }
    (wide_as_nat5 x / pow2 224) / pow2 24;
  (==) { lemma_div224 x }
    (v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280) / pow2 24;
  (==) { }
    (v x4 + (v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 + v x9 * pow2 256) * pow2 24) / pow2 24;
  (==) { FStar.Math.Lemmas.lemma_div_plus (v x4) (v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 + v x9 * pow2 256) (pow2 24) }
    v x4 / pow2 24 + v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 + v x9 * pow2 256;
  }


val lemma_div248_x5: x5:uint64 ->
  Lemma ( pow2 32 * (v x5 % pow2 24) + v x5 / pow2 24 * pow2 56 == v x5 * pow2 32)
let lemma_div248_x5 x5 =
  assert_norm (pow2 32 * pow2 24 = pow2 56)

val lemma_div248_x6: x6:uint64 ->
  Lemma (pow2 32 * (v x6 % pow2 24) * pow2 56 + v x6 / pow2 24 * pow2 112 == v x6 * pow2 88)
let lemma_div248_x6 x6 =
  calc (==) {
    pow2 32 * (v x6 % pow2 24) * pow2 56 + v x6 / pow2 24 * pow2 112;
    (==) { assert_norm (pow2 32 * pow2 56 = pow2 88) }
    (v x6 % pow2 24) * pow2 88 + v x6 / pow2 24 * pow2 112;
    (==) { assert_norm (pow2 112 == pow2 88 * pow2 24) }
    (v x6 % pow2 24) * pow2 88 + v x6 / pow2 24 * pow2 24 * pow2 88;
    (==) { FStar.Math.Lemmas.euclidean_division_definition (v x6) (pow2 24) }
    v x6 * pow2 88;
    }

val lemma_div248_x7: x7:uint64 ->
  Lemma (pow2 32 * (v x7 % pow2 24) * pow2 112 + v x7 / pow2 24 * pow2 168 == v x7 * pow2 144)
let lemma_div248_x7 x7 =
  assert_norm (pow2 32 * pow2 112 = pow2 144);
  assert_norm (pow2 168 == pow2 144 * pow2 24)

val lemma_div248_x8: x8:uint64 ->
  Lemma (pow2 32 * (v x8 % pow2 24) * pow2 168 + v x8 / pow2 24 * pow2 224 == v x8 * pow2 200)
let lemma_div248_x8 x8 =
  calc (==) {
    pow2 32 * (v x8 % pow2 24) * pow2 168 + v x8 / pow2 24 * pow2 224;
    (==) { assert_norm (pow2 32 * pow2 168 = pow2 200) }
    (v x8 % pow2 24) * pow2 200 + v x8 / pow2 24 * pow2 224;
    (==) { assert_norm (pow2 224 == pow2 200 * pow2 24) }
    (v x8 % pow2 24) * pow2 200 + v x8 / pow2 24 * pow2 24 * pow2 200;
    (==) { FStar.Math.Lemmas.euclidean_division_definition (v x8) (pow2 24) }
    v x8 * pow2 200;
    }

val lemma_div248_x9: x9:uint64{v x9 < pow2 24} ->
  Lemma (pow2 32 * (v x9 % pow2 24) * pow2 224 == v x9 * pow2 256)
let lemma_div248_x9 x9 =
  assert_norm (pow2 32 * pow2 224 = pow2 256)

val lemma_wide_as_nat_pow512: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 512)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    v x9 < pow2 24))

let lemma_wide_as_nat_pow512 x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  assert_norm (pow2 504 * pow2 8 = pow2 512);
  FStar.Math.Lemmas.pow2_minus 512 504;
  assert (v x9 < pow2 8);
  assert_norm (pow2 8 < pow2 24)


val lemma_div248: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 512)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    let z0 = v x4 / pow2 24 + pow2 32 * (v x5 % pow2 24) in
    let z1 = v x5 / pow2 24 + pow2 32 * (v x6 % pow2 24) in
    let z2 = v x6 / pow2 24 + pow2 32 * (v x7 % pow2 24) in
    let z3 = v x7 / pow2 24 + pow2 32 * (v x8 % pow2 24) in
    let z4 = v x8 / pow2 24 + pow2 32 * (v x9 % pow2 24) in

    wide_as_nat5 x / pow2 248 == z0 + z1 * pow2 56 + z2 * pow2 112 + z3 * pow2 168 + z4 * pow2 224))

let lemma_div248 x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  lemma_wide_as_nat_pow512 x;
  assert (v x9 < pow2 24);
  let z0 = v x4 / pow2 24 + pow2 32 * (v x5 % pow2 24) in
  let z1 = v x5 / pow2 24 + pow2 32 * (v x6 % pow2 24) in
  let z2 = v x6 / pow2 24 + pow2 32 * (v x7 % pow2 24) in
  let z3 = v x7 / pow2 24 + pow2 32 * (v x8 % pow2 24) in
  let z4 = v x8 / pow2 24 + pow2 32 * (v x9 % pow2 24) in

  calc (==) {
    z0 + z1 * pow2 56 + z2 * pow2 112 + z3 * pow2 168 + z4 * pow2 224;
  (==) { }
    v x4 / pow2 24 + pow2 32 * (v x5 % pow2 24) +
    v x5 / pow2 24 * pow2 56 + pow2 32 * (v x6 % pow2 24) * pow2 56 +
    v x6 / pow2 24 * pow2 112 + pow2 32 * (v x7 % pow2 24) * pow2 112 +
    v x7 / pow2 24 * pow2 168 + pow2 32 * (v x8 % pow2 24) * pow2 168 +
    v x8 / pow2 24 * pow2 224 + pow2 32 * (v x9 % pow2 24) * pow2 224;
  (==) { lemma_div248_x5 x5; lemma_div248_x6 x6 }
    v x4 / pow2 24 + v x5 * pow2 32 + v x6 * pow2 88 +
    pow2 32 * (v x7 % pow2 24) * pow2 112 +
    v x7 / pow2 24 * pow2 168 + pow2 32 * (v x8 % pow2 24) * pow2 168 +
    v x8 / pow2 24 * pow2 224 + pow2 32 * (v x9 % pow2 24) * pow2 224;
  (==) { lemma_div248_x7 x7; lemma_div248_x8 x8 }
    v x4 / pow2 24 + v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 +
    pow2 32 * (v x9 % pow2 24) * pow2 224;
  (==) { lemma_div248_x9 x9 }
    v x4 / pow2 24 + v x5 * pow2 32 + v x6 * pow2 88 + v x7 * pow2 144 + v x8 * pow2 200 + v x9 * pow2 256;
  (==) { lemma_div248_aux x }
    wide_as_nat5 x / pow2 248;
  }


val lemma_add_modq5:
    x:qelem5
  -> y:qelem5
  -> t:qelem5 ->
  Lemma
  (requires
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    qelem_fits5 y (1, 1, 1, 1, 1) /\
    qelem_fits5 t (1, 1, 1, 1, 1) /\
    as_nat5 x < S.q /\ as_nat5 y < S.q /\
    as_nat5 t == as_nat5 x + as_nat5 y)
  (ensures
   (let res = if as_nat5 t >= S.q then as_nat5 t - S.q else as_nat5 t in
    res < S.q /\ res == (as_nat5 x + as_nat5 y) % S.q))

let lemma_add_modq5 x y t =
  assert (as_nat5 t == as_nat5 x + as_nat5 y);
  let res = if as_nat5 t >= S.q then as_nat5 t - S.q else as_nat5 t in
  assert (res < S.q);

  if as_nat5 t >= S.q then (
    FStar.Math.Lemmas.sub_div_mod_1 (as_nat5 t) S.q;
    assert (res % S.q == as_nat5 t % S.q))
  else
    assert (res % S.q == as_nat5 t % S.q);
  FStar.Math.Lemmas.small_mod res S.q


val lemma_wide_as_nat_pow528: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 528)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    v x9 < pow2 40))

let lemma_wide_as_nat_pow528 x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  assert_norm (pow2 504 * pow2 24 = pow2 528);
  FStar.Math.Lemmas.pow2_minus 528 504;
  assert (v x9 < pow2 24);
  assert_norm (pow2 24 < pow2 40)

#push-options "--z3rlimit 200"
val lemma_div264_aux: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 528)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    wide_as_nat5 x / pow2 264 ==
      v x4 / pow2 40 + v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 + v x9 * pow2 240))

let lemma_div264_aux x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  assert_norm (pow2 264 == pow2 224 * pow2 40);
  assert_norm (pow2 56 == pow2 16 * pow2 40);
  assert_norm (pow2 112 == pow2 72 * pow2 40);
  assert_norm (pow2 168 == pow2 128 * pow2 40);
  assert_norm (pow2 224 == pow2 184 * pow2 40);
  assert_norm (pow2 280 == pow2 240 * pow2 40);
  assert_norm (0 < pow2 40);

  calc (==) {
    wide_as_nat5 x / pow2 264;
  (==) { FStar.Math.Lemmas.division_multiplication_lemma (wide_as_nat5 x) (pow2 224) (pow2 40) }
    (wide_as_nat5 x / pow2 224) / pow2 40;
  (==) { lemma_div224 x }
    (v x4 + v x5 * pow2 56 + v x6 * pow2 112 + v x7 * pow2 168 + v x8 * pow2 224 + v x9 * pow2 280) / pow2 40;
  (==) { }
    (v x4 + (v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 + v x9 * pow2 240) * pow2 40) / pow2 40;
  (==) { FStar.Math.Lemmas.lemma_div_plus (v x4) (v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 + v x9 * pow2 240) (pow2 40) }
    v x4 / pow2 40 + v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 + v x9 * pow2 240;
  }
#pop-options


val lemma_div264_x5: x5:uint64 ->
  Lemma (pow2 16 * (v x5 % pow2 40) + v x5 / pow2 40 * pow2 56 == v x5 * pow2 16)
let lemma_div264_x5 x5 =
  calc (==) {
    pow2 16 * (v x5 % pow2 40) + v x5 / pow2 40 * pow2 56;
    (==) { assert_norm (pow2 16 * pow2 40 = pow2 56) }
    pow2 16 * (v x5 % pow2 40) + v x5 / pow2 40 * pow2 40 * pow2 16;
    (==) { }
    v x5 * pow2 16;
    }


val lemma_div264_x6: x6:uint64 ->
  Lemma (pow2 16 * (v x6 % pow2 40) * pow2 56 + v x6 / pow2 40 * pow2 112 == v x6 * pow2 72)
let lemma_div264_x6 x6 =
  calc (==) {
    pow2 16 * (v x6 % pow2 40) * pow2 56 + v x6 / pow2 40 * pow2 112;
    (==) { assert_norm (pow2 16 * pow2 56 = pow2 72) }
    pow2 72 * (v x6 % pow2 40) + v x6 / pow2 40 * pow2 112;
    (==) { assert_norm (pow2 72 * pow2 40 = pow2 112) }
    pow2 72 * (v x6 % pow2 40) + v x6 / pow2 40 * pow2 72 * pow2 40;
    (==) { FStar.Math.Lemmas.euclidean_division_definition (v x6) (pow2 40) }
    v x6 * pow2 72;
    }


val lemma_div264_x7: x7:uint64 ->
  Lemma (pow2 16 * (v x7 % pow2 40) * pow2 112 + v x7 / pow2 40 * pow2 168 == v x7 * pow2 128)
let lemma_div264_x7 x7 =
  calc (==) {
    pow2 16 * (v x7 % pow2 40) * pow2 112 + v x7 / pow2 40 * pow2 168;
    (==) { assert_norm (pow2 16 * pow2 112 = pow2 128) }
    pow2 128 * (v x7 % pow2 40) + v x7 / pow2 40 * pow2 168;
    (==) { assert_norm (pow2 128 * pow2 40 = pow2 168) }
    pow2 128 * (v x7 % pow2 40) + v x7 / pow2 40 * pow2 128 * pow2 40;
    (==) { }
    v x7 * pow2 128;
    }


val lemma_div264_x8: x8:uint64 ->
  Lemma (pow2 16 * (v x8 % pow2 40) * pow2 168 + v x8 / pow2 40 * pow2 224 == v x8 * pow2 184)
let lemma_div264_x8 x8 =
  calc (==) {
    pow2 16 * (v x8 % pow2 40) * pow2 168 + v x8 / pow2 40 * pow2 224;
    (==) { assert_norm (pow2 16 * pow2 168 = pow2 184) }
    pow2 184 * (v x8 % pow2 40) + v x8 / pow2 40 * pow2 224;
    (==) { assert_norm (pow2 184 * pow2 40 = pow2 224) }
    pow2 184 * (v x8 % pow2 40) + v x8 / pow2 40 * pow2 184 * pow2 40;
    (==) { }
    v x8 * pow2 184;
    }


val lemma_div264_x9: x9:uint64{v x9 < pow2 40} ->
  Lemma (pow2 16 * (v x9 % pow2 40) * pow2 224 == v x9 * pow2 240)
let lemma_div264_x9 x9 =
  assert_norm (pow2 16 * pow2 224 = pow2 240)


val lemma_div264: x:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 x (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat5 x < pow2 528)
  (ensures
   (let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
    let z0 = v x4 / pow2 40 + pow2 16 * (v x5 % pow2 40) in
    let z1 = v x5 / pow2 40 + pow2 16 * (v x6 % pow2 40) in
    let z2 = v x6 / pow2 40 + pow2 16 * (v x7 % pow2 40) in
    let z3 = v x7 / pow2 40 + pow2 16 * (v x8 % pow2 40) in
    let z4 = v x8 / pow2 40 + pow2 16 * (v x9 % pow2 40) in

    wide_as_nat5 x / pow2 264 == z0 + z1 * pow2 56 + z2 * pow2 112 + z3 * pow2 168 + z4 * pow2 224))

let lemma_div264 x =
  let (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) = x in
  lemma_wide_as_nat_pow528 x;
  assert (v x9 < pow2 40);
  let z0 = v x4 / pow2 40 + pow2 16 * (v x5 % pow2 40) in
  let z1 = v x5 / pow2 40 + pow2 16 * (v x6 % pow2 40) in
  let z2 = v x6 / pow2 40 + pow2 16 * (v x7 % pow2 40) in
  let z3 = v x7 / pow2 40 + pow2 16 * (v x8 % pow2 40) in
  let z4 = v x8 / pow2 40 + pow2 16 * (v x9 % pow2 40) in

  calc (==) {
    z0 + z1 * pow2 56 + z2 * pow2 112 + z3 * pow2 168 + z4 * pow2 224;
  (==) { }
    v x4 / pow2 40 + pow2 16 * (v x5 % pow2 40) +
    v x5 / pow2 40 * pow2 56 + pow2 16 * (v x6 % pow2 40) * pow2 56 +
    v x6 / pow2 40 * pow2 112 + pow2 16 * (v x7 % pow2 40) * pow2 112 +
    v x7 / pow2 40 * pow2 168 + pow2 16 * (v x8 % pow2 40) * pow2 168 +
    v x8 / pow2 40 * pow2 224 + pow2 16 * (v x9 % pow2 40) * pow2 224;
  (==) { lemma_div264_x5 x5; lemma_div264_x6 x6 }
    v x4 / pow2 40 + v x5 * pow2 16 + v x6 * pow2 72 +
    pow2 16 * (v x7 % pow2 40) * pow2 112 +
    v x7 / pow2 40 * pow2 168 + pow2 16 * (v x8 % pow2 40) * pow2 168 +
    v x8 / pow2 40 * pow2 224 + pow2 16 * (v x9 % pow2 40) * pow2 224;
  (==) { lemma_div264_x7 x7; lemma_div264_x8 x8 }
    v x4 / pow2 40 + v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 +
    pow2 16 * (v x9 % pow2 40) * pow2 224;
  (==) { lemma_div264_x9 x9 }
    v x4 / pow2 40 + v x5 * pow2 16 + v x6 * pow2 72 + v x7 * pow2 128 + v x8 * pow2 184 + v x9 * pow2 240;
  (==) { lemma_div264_aux x }
    wide_as_nat5 x / pow2 264;
  }


val lemma_mod_264_aux: t:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 t (1, 1, 1, 1, 1, 1, 1, 1, 1, 1))
  (ensures
   (let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) = t in
   (wide_as_nat5 t) % pow2 264 ==
   (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224) % pow2 264))

let lemma_mod_264_aux t =
  let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) = t in
  let res = (t0, t1, t2, t3, t4 &. u64 0xffffffffff) in

  assert_norm (pow2 16 * pow2 264 == pow2 280);
  assert_norm (pow2 72 * pow2 264 == pow2 336);
  assert_norm (pow2 128 * pow2 264 == pow2 392);
  assert_norm (pow2 184 * pow2 264 == pow2 448);
  assert_norm (pow2 240 * pow2 264 == pow2 504);

  calc (==) {
    (wide_as_nat5 t) % pow2 264;
  (==) { }
    (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224 +
     (v t5 * pow2 16 + v t6 * pow2 72 + v t7 * pow2 128 + v t8 * pow2 184 + v t9 * pow2 240) * pow2 264) % pow2 264;
  (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224)
    ((v t5 * pow2 16 + v t6 * pow2 72 + v t7 * pow2 128 + v t8 * pow2 184 + v t9 * pow2 240) * pow2 264) (pow2 264)}
    ((v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224) +
     ((v t5 * pow2 16 + v t6 * pow2 72 + v t7 * pow2 128 + v t8 * pow2 184 + v t9 * pow2 240) * pow2 264) % pow2 264) % pow2 264;
  (==) { FStar.Math.Lemmas.cancel_mul_mod (v t5 * pow2 16 + v t6 * pow2 72 + v t7 * pow2 128 + v t8 * pow2 184 + v t9 * pow2 240) (pow2 264) }
    (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224) % pow2 264;
  }


val lemma_as_nat_pow264: x:qelem5 ->
  Lemma
  (requires
   (let (x0, x1, x2, x3, x4) = x in
    qelem_fits5 x (1, 1, 1, 1, 1) /\
    v x4 < pow2 40))
  (ensures as_nat5 x < pow2 264)

let lemma_as_nat_pow264 x =
  let (x0, x1, x2, x3, x4) = x in
  assert_norm (pow2 40 * pow2 224 = pow2 264)


val lemma_mod_264: t:qelem_wide5 ->
  Lemma
  (requires
    qelem_wide_fits5 t (1, 1, 1, 1, 1, 1, 1, 1, 1, 1))
  (ensures
   (let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) = t in
    let res = (t0, t1, t2, t3, t4 &. u64 0xffffffffff) in
    qelem_fits5 res (1, 1, 1, 1, 1) /\
    as_nat5 res == (wide_as_nat5 t) % pow2 264))

let lemma_mod_264 t =
  let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) = t in
  let t4' = t4 &. u64 0xffffffffff in
  let res = (t0, t1, t2, t3, t4') in
  assert_norm (pow2 40 < pow2 64);
  assert_norm (pow2 40 - 1 == 0xffffffffff);
  mod_mask_lemma t4 40ul;
  assert (v (mod_mask #U64 #SEC 40ul) == 0xffffffffff);
  assert (v (t4 &. u64 0xffffffffff) == v t4 % pow2 40);

  calc (==) {
    (wide_as_nat5 t) % pow2 264;
    (==) { lemma_mod_264_aux t }
    (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + v t4 * pow2 224) % pow2 264;
    (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168) (v t4 * pow2 224) (pow2 264) }
    (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + (v t4 * pow2 224) % pow2 264) % pow2 264;
    (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v t4) 264 224 }
    (v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + (v t4 % pow2 40) * pow2 224) % pow2 264;
    (==) { lemma_as_nat_pow264 res; FStar.Math.Lemmas.modulo_lemma (as_nat5 res) (pow2 264) }
    v t0 + v t1 * pow2 56 + v t2 * pow2 112 + v t3 * pow2 168 + (v t4 % pow2 40) * pow2 224;
    }
