module Hacl.Spec.K256.Field52.Lemmas

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

///  Load and store functions

val load_felem5_lemma_as_nat: s:felem4 -> f:felem5 -> Lemma
  (requires
   (let (s0,s1,s2,s3) = s in
    let (f0,f1,f2,f3,f4) = f in
    v f0 == v s0 % pow2 52 /\
    v f1 == v s0 / pow2 52 + v s1 % pow2 40 * pow2 12 /\
    v f2 == v s1 / pow2 40 + v s2 % pow2 28 * pow2 24 /\
    v f3 == v s2 / pow2 28 + v s3 % pow2 16 * pow2 36 /\
    v f4 == v s3 / pow2 16))
  (ensures
    as_nat5 f == as_nat4 s)

let load_felem5_lemma_as_nat s f =
  let (s0,s1,s2,s3) = s in
  let (f0,f1,f2,f3,f4) = f in
  Math.Lemmas.euclidean_division_definition (v s0) (pow2 52);
  assert_norm (pow2 12 * pow2 52 = pow2 64);
  assert_norm (pow2 52 * pow2 52 = pow2 40 * pow2 64);
  Math.Lemmas.euclidean_division_definition (v s1) (pow2 40);
  assert_norm (pow2 24 * pow2 52 * pow2 52 = pow2 128);
  assert_norm (pow2 52 * pow2 52 * pow2 52 = pow2 28 * pow2 128);
  Math.Lemmas.euclidean_division_definition (v s2) (pow2 25);
  assert_norm (pow2 36 * pow2 52 * pow2 52 * pow2 52 = pow2 192);
  assert_norm (pow2 52 * pow2 52 * pow2 52 * pow2 52 = pow2 16 * pow2 192);
  Math.Lemmas.euclidean_division_definition (v s3) (pow2 16);
  assert (as_nat5 f == v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192)


val lemma_a_div_b_plus_c_mod_d_mul_e (a b c d e:nat) : Lemma
  (requires a / pow2 b < pow2 e)
  (ensures  a / pow2 b + c % pow2 d * pow2 e < pow2 (d + e))

let lemma_a_div_b_plus_c_mod_d_mul_e a b c d e =
  let t_r = c % pow2 d * pow2 e in
  Math.Lemmas.lemma_mult_le_right (pow2 e) (c % pow2 d) (pow2 d - 1);
  assert (t_r <= (pow2 d - 1) * pow2 e);
  assert (t_r <= pow2 d * pow2 e - pow2 e);
  Math.Lemmas.pow2_plus d e;
  assert (t_r <= pow2 (d + e) - pow2 e);
  assert (a / pow2 b + c % pow2 d * pow2 e < pow2 (d + e))


val load_felem5_lemma_fits: s:felem4 -> f:felem5 -> Lemma
  (requires
   (let (s0,s1,s2,s3) = s in
    let (f0,f1,f2,f3,f4) = f in
    v f0 == v s0 % pow2 52 /\
    v f1 == v s0 / pow2 52 + v s1 % pow2 40 * pow2 12 /\
    v f2 = v s1 / pow2 40 + v s2 % pow2 28 * pow2 24 /\
    v f3 = v s2 / pow2 28 + v s3 % pow2 16 * pow2 36 /\
    v f4 = v s3 / pow2 16))
  (ensures felem_fits5 f (1,1,1,1,1))

let load_felem5_lemma_fits s f =
  let (s0,s1,s2,s3) = s in
  let (f0,f1,f2,f3,f4) = f in
  assert (v f0 < pow2 52);

  Math.Lemmas.lemma_div_lt (v s0) 64 52;
  lemma_a_div_b_plus_c_mod_d_mul_e (v s0) 52 (v s1) 40 12;
  assert (v f1 < pow2 52);

  Math.Lemmas.lemma_div_lt (v s1) 64 40;
  lemma_a_div_b_plus_c_mod_d_mul_e (v s1) 40 (v s2) 28 24;
  assert (v f2 < pow2 52);

  Math.Lemmas.lemma_div_lt (v s2) 64 28;
  lemma_a_div_b_plus_c_mod_d_mul_e (v s2) 28 (v s3) 16 36;
  assert (v f3 < pow2 52);

  assert (v f4 = v s3 / pow2 16);
  Math.Lemmas.lemma_div_lt (v s3) 64 16;
  assert (v f4 < pow2 48)


val lemma_a_mod_b_mul_c_mod_d (a b c d:nat) : Lemma
  (requires c <= d /\ b <= d - c)
  (ensures  (a % pow2 b) * pow2 c % pow2 d = (a % pow2 b) * pow2 c)

let lemma_a_mod_b_mul_c_mod_d a b c d =
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (a % pow2 b) d c;
  Math.Lemmas.pow2_modulo_modulo_lemma_2 a (d - c) b


let load_felem5_lemma s =
  assert_norm (v mask52 = pow2 52 - 1);
  assert_norm (0xffffffffff = pow2 40 - 1);
  assert_norm (0xfffffff = pow2 28 - 1);
  assert_norm (0xffff = pow2 16 - 1);

  let (s0,s1,s2,s3) = s in
  let f0 = s0 &. mask52 in // s0 % pow2 52
  mod_mask_lemma s0 52ul;
  assert (v (mod_mask #U64 #SEC 52ul) == v mask52);
  assert (v f0 = v s0 % pow2 52);

  let f11 = s0 >>. 52ul in
  let f12 = (s1 &. u64 0xffffffffff) <<. 12ul in
  let f1 = f11 |. f12 in // s0 / pow2 52 + (s1 % pow2 40) * pow2 12
  Math.Lemmas.lemma_div_lt (v s0) 64 52;
  //assert (v f11 < pow2 12);
  mod_mask_lemma s1 40ul;
  assert (v (mod_mask #U64 #SEC 40ul) == 0xffffffffff);
  lemma_a_mod_b_mul_c_mod_d (v s1) 40 12 64;
  //assert (v f12 == v s1 % pow2 40 * pow2 12);
  Math.Lemmas.cancel_mul_mod (v s1 % pow2 40) (pow2 12);
  logor_disjoint f11 f12 12;
  assert (v f1 = v s0 / pow2 52 + v s1 % pow2 40 * pow2 12);

  let f21 = s1 >>. 40ul in
  let f22 = (s2 &. u64 0xfffffff) <<. 24ul in
  let f2 = f21 |. f22 in // s1 / pow2 40 + (s2 % pow2 28) * pow2 24
  Math.Lemmas.lemma_div_lt (v s1) 64 40;
  //assert (v f21 < pow2 24);
  mod_mask_lemma s2 28ul;
  assert (v (mod_mask #U64 #SEC 28ul) == 0xfffffff);
  lemma_a_mod_b_mul_c_mod_d (v s2) 28 24 64;
  //assert (v f22 == v s2 % pow2 28 * pow2 24);
  Math.Lemmas.cancel_mul_mod (v s2 % pow2 28) (pow2 24);
  logor_disjoint f21 f22 24;
  assert (v f2 = v s1 / pow2 40 + v s2 % pow2 28 * pow2 24);

  let f31 = s2 >>. 28ul in
  let f32 = (s3 &. u64 0xffff) <<. 36ul in
  let f3 = f31 |. f32 in // s2 / pow2 28 + (s3 % pow2 16) * pow2 36
  Math.Lemmas.lemma_div_lt (v s2) 64 28;
  //assert (v f31 < pow2 36);
  mod_mask_lemma s3 16ul;
  assert (v (mod_mask #U64 #SEC 16ul) == 0xffff);
  lemma_a_mod_b_mul_c_mod_d (v s3) 16 36 64;
  //assert (v f32 == v s3 % pow2 16 * pow2 36);
  Math.Lemmas.cancel_mul_mod (v s3 % pow2 16) (pow2 36);
  logor_disjoint f31 f32 36;
  assert (v f3 = v s2 / pow2 28 + v s3 % pow2 16 * pow2 36);

  let f4 = s3 >>. 16ul in // s3 / pow2 16
  assert (v f4 = v s3 / pow2 16);

  let f = (f0,f1,f2,f3,f4) in
  load_felem5_lemma_as_nat s f;
  load_felem5_lemma_fits s f


val lemma_a_mul_c_plus_d_mod_e_mul_f_g (a b c d f g:nat) : Lemma
  (requires c == g - b)
  (ensures
    a % pow2 b * pow2 c + (a / pow2 b + d * pow2 f) * pow2 g ==
    a * pow2 c + d * pow2 (f + g))

let lemma_a_mul_c_plus_d_mod_e_mul_f_g a b c d f g =
  calc (==) {
    a % pow2 b * pow2 c + (a / pow2 b + d * pow2 f) * pow2 g;
    (==) {
      Math.Lemmas.distributivity_add_left (a / pow2 b) (d * pow2 f) (pow2 g);
      Math.Lemmas.paren_mul_right (d) (pow2 f) (pow2 g);
      Math.Lemmas.pow2_plus f g }
    a % pow2 b * pow2 c + a / pow2 b * pow2 g + d * pow2 (f + g);
    (==) {
      Math.Lemmas.pow2_plus b (g - b);
      Math.Lemmas.paren_mul_right (a / pow2 b) (pow2 b) (g - b) }
    a % pow2 b * pow2 c + a / pow2 b * pow2 b * pow2 c + d * pow2 (f + g);
    (==) {
      Math.Lemmas.distributivity_add_left (a % pow2 b) (a / pow2 b * pow2 b) (pow2 c);
      Math.Lemmas.euclidean_division_definition a (pow2 b) }
    a * pow2 c + d * pow2 (f + g);
  }


val store_felem5_lemma_as_nat: f:felem5 -> s:felem4 -> Lemma
  (requires
   (let (f0,f1,f2,f3,f4) = f in
    let (s0,s1,s2,s3) = s in
    felem_fits5 f (1,1,1,1,1) /\
    v s0 == v f0 + v f1 % pow2 12 * pow2 52 /\
    v s1 == v f1 / pow2 12 + v f2 % pow2 24 * pow2 40 /\
    v s2 == v f2 / pow2 24 + v f3 % pow2 36 * pow2 28 /\
    v s3 == v f3 / pow2 36 + v f4 % pow2 48 * pow2 16))
  (ensures as_nat4 s == as_nat5 f)

let store_felem5_lemma_as_nat f s =
  let (f0,f1,f2,f3,f4) = f in
  let (s0,s1,s2,s3) = s in
  assert (as_nat4 s == v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192);

  calc (==) {
    v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192;
    (==) { }
    v f0 + v f1 % pow2 12 * pow2 52 + (v f1 / pow2 12 + v f2 % pow2 24 * pow2 40) * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192;
    (==) { lemma_a_mul_c_plus_d_mod_e_mul_f_g (v f1) 12 52 (v f2 % pow2 24) 40 64 }
    v f0 + v f1 * pow2 52 + v f2 % pow2 24 * pow2 104 + (v f2 / pow2 24 + v f3 % pow2 36 * pow2 28) * pow2 128 + v s3 * pow2 192;
    (==) { lemma_a_mul_c_plus_d_mod_e_mul_f_g (v f2) 24 104 (v f3 % pow2 36) 28 128 }
    v f0 + v f1 * pow2 52 + v f2 * pow2 104 + v f3 % pow2 36 * pow2 156 + (v f3 / pow2 36 + v f4 % pow2 48 * pow2 16) * pow2 192;
    (==) { lemma_a_mul_c_plus_d_mod_e_mul_f_g (v f3) 36 156 (v f4 % pow2 48) 16 192 }
    v f0 + v f1 * pow2 52 + v f2 * pow2 104 + v f3 * pow2 156 + (v f4 % pow2 48) * pow2 208;
    (==) { Math.Lemmas.small_mod (v f4) (pow2 48) }
    v f0 + v f1 * pow2 52 + v f2 * pow2 104 + v f3 * pow2 156 + v f4 * pow2 208;
    }


let store_felem5_lemma f =
  let (f0,f1,f2,f3,f4) = f in
  let o0 = f0 |. (f1 <<. 52ul) in
  //assert (v (f1 <<. 52ul) == v f1 * pow2 52 % pow2 64);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f1) 64 52;
  //assert (v (f1 <<. 52ul) == v f1 % pow2 12 * pow2 52);
  Math.Lemmas.cancel_mul_mod (v f1 % pow2 12) (pow2 52);
  logor_disjoint f0 (f1 <<. 52ul) 52;
  assert (v o0 == v f0 + v f1 % pow2 12 * pow2 52);

  let o1 = (f1 >>. 12ul) |. (f2 <<. 40ul) in
  //assert (v (f1 >>. 12ul) == v f1 / pow2 12);
  Math.Lemmas.lemma_div_lt (v f1) 52 12;
  //assert (v (f2 <<. 40ul) == v f2 * pow2 40 % pow2 64);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f2) 64 40;
  assert (v (f2 <<. 40ul) == v f2 % pow2 24 * pow2 40);
  Math.Lemmas.cancel_mul_mod (v f2 % pow2 24) (pow2 40);
  logor_disjoint (f1 >>. 12ul) (f2 <<. 40ul) 40;
  assert (v o1 == v f1 / pow2 12 + v f2 % pow2 24 * pow2 40);

  let o2 = (f2 >>. 24ul) |. (f3 <<. 28ul) in
  Math.Lemmas.lemma_div_lt (v f2) 52 24;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f3) 64 28;
  //assert (v (f3 <<. 28ul) == v f3 % pow2 36 * pow2 28);
  Math.Lemmas.cancel_mul_mod (v f3 % pow2 36) (pow2 28);
  logor_disjoint (f2 >>. 24ul) (f3 <<. 28ul) 28;
  assert (v o2 == v f2 / pow2 24 + v f3 % pow2 36 * pow2 28);

  let o3 = (f3 >>. 36ul) |. (f4 <<. 16ul) in
  Math.Lemmas.lemma_div_lt (v f3) 52 36;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 64 16;
  //assert (v (f4 <<. 16ul) == v f4 % pow2 48 * pow2 16);
  Math.Lemmas.cancel_mul_mod (v f4 % pow2 48) (pow2 16);
  logor_disjoint (f3 >>. 36ul) (f4 <<. 16ul) 16;
  assert (v o3 == v f3 / pow2 36 + v f4 % pow2 48 * pow2 16);
  store_felem5_lemma_as_nat f (o0,o1,o2,o3)


///  Addition and multiplication by a digit

val add5_lemma1: ma:scale64 -> mb:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a ma /\ felem_fits1 b mb /\ ma + mb <= 4096)
  (ensures  v (a +. b) == v a + v b /\ felem_fits1 (a +. b) (ma + mb))

let add5_lemma1 ma mb a b =
  assert (v a + v b <= (ma + mb) * max52);
  Math.Lemmas.lemma_mult_le_right max52 (ma + mb) 4096;
  assert (v a + v b <= 4096 * max52);
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a + v b) (pow2 64)


val add5_lemma_last1: ma:scale64_last -> mb:scale64_last -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits_last1 a ma /\ felem_fits_last1 b mb /\ ma + mb <= 65536)
  (ensures  v (a +. b) == v a + v b /\ felem_fits_last1 (a +. b) (ma + mb))

let add5_lemma_last1 ma mb a b =
  assert (v a + v b <= (ma + mb) * max48);
  Math.Lemmas.lemma_mult_le_right max48 (ma + mb) 65536;
  assert (v a + v b <= 65536 * max48);
  assert_norm (65536 * max48 < pow2 64);
  Math.Lemmas.small_mod (v a + v b) (pow2 64)


let add5_lemma m1 m2 f1 f2 =
  let (a0,a1,a2,a3,a4) = f1 in
  let (b0,b1,b2,b3,b4) = f2 in
  let (ma0,ma1,ma2,ma3,ma4) = m1 in
  let (mb0,mb1,mb2,mb3,mb4) = m2 in
  add5_lemma1 ma0 mb0 a0 b0;
  add5_lemma1 ma1 mb1 a1 b1;
  add5_lemma1 ma2 mb2 a2 b2;
  add5_lemma1 ma3 mb3 a3 b3;
  add5_lemma_last1 ma4 mb4 a4 b4


let fadd5_lemma m1 m2 f1 f2 =
  let r = add5 f1 f2 in
  add5_lemma m1 m2 f1 f2;
  assert (as_nat5 r == as_nat5 f1 + as_nat5 f2);
  Math.Lemmas.modulo_distributivity (as_nat5 f1) (as_nat5 f2) S.prime


val mul15_lemma1: ma:scale64 -> mb:nat -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a ma /\ v b <= mb /\ ma * mb <= 4096)
  (ensures  v (a *. b) == v a * v b /\ felem_fits1 (a *. b) (ma * mb))

let mul15_lemma1 ma mb a b =
  assert (v a * v b <= (ma * mb) * max52);
  Math.Lemmas.lemma_mult_le_right max52 (ma * mb) 4096;
  assert (v a * v b <= 4096 * max52);
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a * v b) (pow2 64)


val mul15_lemma_last1: ma:scale64_last -> mb:nat -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits_last1 a ma /\ v b <= mb /\ ma * mb <= 65536)
  (ensures  v (a *. b) == v a * v b /\ felem_fits_last1 (a *. b) (ma * mb))

let mul15_lemma_last1 ma mb a b =
  assert (v a * v b <= (ma * mb) * max48);
  Math.Lemmas.lemma_mult_le_right max48 (ma * mb) 65536;
  assert (v a * v b <= 65536 * max48);
  assert_norm (65536 * max48 < pow2 64);
  Math.Lemmas.small_mod (v a * v b) (pow2 64)


val lemma_a_mul_c_plus_b_mul_c_mul_d (a b c d: nat) :
  Lemma (b * a + c * b * d == b * (a + c * d))

let lemma_a_mul_c_plus_b_mul_c_mul_d a b c d =
  Math.Lemmas.swap_mul c b;
  Math.Lemmas.paren_mul_right b c d;
  Math.Lemmas.distributivity_add_right b a (c * d)


let mul15_lemma m1 m2 f c =
  let (f0,f1,f2,f3,f4) = f in
  let (mf0,mf1,mf2,mf3,mf4) = m1 in
  mul15_lemma1 mf0 m2 f0 c;
  mul15_lemma1 mf1 m2 f1 c;
  mul15_lemma1 mf2 m2 f2 c;
  mul15_lemma1 mf3 m2 f3 c;
  mul15_lemma_last1 mf4 m2 f4 c;

  calc (==) {
    v f0 * v c + v f1 * v c * pow52 + v f2 * v c * pow104 + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0) (v c) (v f1) pow52 }
    v c * (v f0 + v f1 * pow52) + v f2 * v c * pow104 + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52) (v c) (v f2) pow104 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104) + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52 + v f2 * pow104) (v c) (v f3) pow156 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156) + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156) (v c) (v f4) pow208 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208);
  }


let fmul15_lemma m1 m2 f c =
  let r = mul15 f c in
  mul15_lemma m1 m2 f c;
  assert (as_nat5 r == as_nat5 f * v c);
  Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 f) (v c) S.prime


let lemma_as_nat_bound f =
  let (f0,f1,f2,f3,f4) = f in
  calc (<=) { //as_nat5 f ==
    v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208;
    (<=) { }
    pow2 52 - 1 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow52 (v f1) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow52 }
    pow2 52 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow104 (v f2) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow104;
      Math.Lemmas.pow2_plus 52 52 }
    pow2 52 * pow104 + v f3 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow156 (v f3) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow156;
      Math.Lemmas.pow2_plus 52 104 }
    pow2 52 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow208 (v f4) (pow2 48 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 48) 1 pow208;
      Math.Lemmas.pow2_plus 48 156;
      Math.Lemmas.pow2_plus 48 208 }
    pow2 256 - 1;
  }


let lemma_as_nat_decompose f =
  let (f0,f1,f2,f3,f4) = f in
  lemma_as_nat_bound f;

  Math.Lemmas.euclidean_division_definition (as_nat5 f) pow208;
  assert (v f4 = as_nat5 f / pow208);

  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow208) pow156;
  assert (v f3 = as_nat5 f % pow208 / pow156);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 156 208;
  assert (as_nat5 f % pow208 % pow156 == as_nat5 f % pow156);
  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow156) pow104;
  assert (v f2 = as_nat5 f % pow156 / pow104);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 104 156;
  assert (as_nat5 f % pow156 % pow104 == as_nat5 f % pow104);
  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow104) pow52;
  assert (v f1 = as_nat5 f % pow104 / pow52);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 52 104;
  assert (as_nat5 f % pow104 % pow52 == as_nat5 f % pow52);
  assert (v f0 = as_nat5 f % pow52)


#set-options "--ifuel 1"

let as_nat_inj f1 f2 =
  lemma_as_nat_decompose f1;
  lemma_as_nat_decompose f2


let is_felem_zero_vartime5_lemma f = ()


let is_felem_ge_prime_vartime5_lemma f =
  assert_norm (S.prime =
    0xffffefffffc2f + 0xfffffffffffff * pow52 + 0xfffffffffffff * pow104 +
    0xfffffffffffff * pow156 + 0xffffffffffff * pow208);
  lemma_as_nat_bound f


let is_felem_lt_vartime5_lemma f1 f2 = ()


let is_felem_lt_prime_minus_order_vartime5_lemma f =
  assert_norm (S.prime - S.q =
    0xda1722fc9baee + 0x1950b75fc4402 * pow52 + 0x1455123 * pow104)


let is_felem_eq_vartime5_lemma f1 f2 =
  if as_nat5 f1 = as_nat5 f2 then as_nat_inj f1 f2

#set-options "--ifuel 0"

val lemma_prime : unit -> Lemma (pow2 256 % S.prime = 0x1000003D1)
let lemma_prime () = ()


val lemma_a_plus_b_mul_pow256 (a b:nat) :
  Lemma ((a + b * pow2 256) % S.prime == (a + b * 0x1000003D1) % S.prime)

let lemma_a_plus_b_mul_pow256 a b =
  calc (==) {
    (a + b * pow2 256) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r a (b * pow2 256) S.prime }
    (a + b * pow2 256 % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r b (pow2 256) S.prime }
    (a + b * (pow2 256 % S.prime) % S.prime) % S.prime;
    (==) { lemma_prime () }
    (a + b * 0x1000003D1 % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r a (b * 0x1000003D1) S.prime }
    (a +b * 0x1000003D1) % S.prime;
  }


val as_nat_mod_prime (t0 t1 t2 t3 t4:nat) : Lemma
  ((t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208) % S.prime =
   (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + (t4 % pow2 48) * pow208 + t4 / pow2 48 * 0x1000003D1) % S.prime)

let as_nat_mod_prime t0 t1 t2 t3 t4 =
  calc (==) {
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208) % S.prime;
    (==) { Math.Lemmas.euclidean_division_definition t4 (pow2 48) }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + (t4 / pow2 48 * pow2 48 + t4 % pow2 48) * pow208) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left (t4 / pow2 48 * pow2 48) (t4 % pow2 48) pow208 }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 / pow2 48 * pow2 48 * pow208 + t4 % pow2 48 * pow208) % S.prime;
    (==) {
      Math.Lemmas.paren_mul_right (t4 / pow2 48) (pow2 48) pow208;
      Math.Lemmas.pow2_plus 48 208 }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 / pow2 48 * pow2 256 + t4 % pow2 48 * pow208) % S.prime;
    (==) { lemma_a_plus_b_mul_pow256 (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 % pow2 48 * pow208) (t4 / pow2 48) }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 % pow2 48 * pow208 + t4 / pow2 48 * 0x1000003D1) % S.prime;
  }


inline_for_extraction noextract
let last_carry_mod_prime5 ((t0,t1,t2,t3,t4):felem5) : felem5 =
  let x = t4 >>. 48ul in let t4 = t4 &. mask48 in
  let t0 = t0 +. x *. u64 0x1000003D1 in
  (t0,t1,t2,t3,t4)


val last_carry_mod_prime5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ felem_fits5 f m))
  (ensures
   (let r = last_carry_mod_prime5 f in
    let (m0,m1,m2,m3,m4) = m in
    as_nat5 r % S.prime == as_nat5 f % S.prime /\
    felem_fits5 r (m0+1,m1,m2,m3,1)))

let last_carry_mod_prime5_lemma m f =
  let r = last_carry_mod_prime5 f in
  let (m0,m1,m2,m3,m4) = m in
  let (t0,t1,t2,t3,t4) = f in

  let x = t4 >>. 48ul in let t4' = t4 &. mask48 in
  assert_norm (v mask48 = pow2 48 - 1);
  mod_mask_lemma t4 48ul;
  assert (v (mod_mask #U64 #SEC 48ul) == v mask48);
  assert (v t4' = v t4 % pow2 48);
  assert (felem_fits_last1 t4' 1);

  assert (v x = v t4 / pow2 48);
  Math.Lemmas.lemma_div_lt (v t4) 64 48;
  assert (v x < pow2 16);
  Math.Lemmas.lemma_mult_lt_right 0x1000003D1 (v x) (pow2 16);
  assert_norm (pow2 16 * 0x1000003D1 < max52);
  assert (v t0 + v x * 0x1000003D1 < (m0 + 1) * max52);
  Math.Lemmas.lemma_mult_le_right max52 (m0 + 1) 4096;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v t0 + v x * 0x1000003D1) (pow2 64);
  let t0' = t0 +. x *. u64 0x1000003D1 in
  assert (v t0' = v t0 + v x * 0x1000003D1);
  assert (felem_fits1 t0' (m0 + 1));

  assert (as_nat5 r =
    v t0 + v t4 / pow2 48 * 0x1000003D1 + v t1 * pow52 + v t2 * pow104 +
    v t3 * pow156 + (v t4 % pow2 48) * pow208);

  as_nat_mod_prime (v t0) (v t1) (v t2) (v t3) (v t4);
  assert (as_nat5 r % S.prime == as_nat5 f % S.prime)


val lemma_carry52: m1:scale64 -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 4096)
  (ensures
    (let c = a +. (b >>. 52ul) in let d = b &. mask52 in
     felem_fits1 d 1 /\ felem_fits1 c (m1 + 1) /\
     v d = v b % pow2 52 /\ v c = v a + (v b / pow2 52)))

let lemma_carry52 m1 m2 a b =
  let c = a +. (b >>. 52ul) in let d = b &. mask52 in

  assert_norm (v mask52 = pow2 52 - 1);
  mod_mask_lemma b 52ul;
  assert (v (mod_mask #U64 #SEC 52ul) == v mask52);
  assert (v d = v b % pow2 52);
  assert (felem_fits1 d 1);

  Math.Lemmas.lemma_div_lt (v b) 64 52;
  assert (v b / pow2 52 < pow2 12);
  assert (v a + v b / pow2 52 <= m1 * max52 + pow2 12);
  assert_norm (pow2 12 < max52);
  assert (v a + v b / pow2 52 < (m1 + 1) * max52);
  Math.Lemmas.lemma_mult_le_right max52 (m1 + 1) 4096;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a + v b / pow2 52) (pow2 64);
  assert (v c = v a + v b / pow2 52);
  assert (felem_fits1 c (m1 + 1))


val lemma_carry_last52: m1:scale64_last -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits_last1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 65536)
  (ensures
    (let c = a +. (b >>. 52ul) in let d = b &. mask52 in
     felem_fits1 d 1 /\ felem_fits_last1 c (m1 + 1) /\
     v d = v b % pow2 52 /\ v c = v a + (v b / pow2 52)))

let lemma_carry_last52 m1 m2 a b =
  let c = a +. (b >>. 52ul) in let d = b &. mask52 in

  assert_norm (v mask52 = pow2 52 - 1);
  mod_mask_lemma b 52ul;
  assert (v (mod_mask #U64 #SEC 52ul) == v mask52);
  assert (v d = v b % pow2 52);
  assert (felem_fits1 d 1);

  Math.Lemmas.lemma_div_lt (v b) 64 52;
  assert (v b / pow2 52 < pow2 12);
  assert (v a + v b / pow2 52 <= m1 * max48 + pow2 12);
  assert_norm (pow2 12 < max48);
  assert (v a + v b / pow2 52 < (m1 + 1) * max48);
  Math.Lemmas.lemma_mult_le_right max48 (m1 + 1) 65536;
  assert_norm (65536 * max48 < pow2 64);
  Math.Lemmas.small_mod (v a + v b / pow2 52) (pow2 64);
  assert (v c = v a + v b / pow2 52);
  assert (felem_fits_last1 c (m1 + 1))


inline_for_extraction noextract
let carry_round5 ((t0,t1,t2,t3,t4):felem5) : felem5 =
  let t1 = t1 +. (t0 >>. 52ul) in let t0 = t0 &. mask52 in
  let t2 = t2 +. (t1 >>. 52ul) in let t1 = t1 &. mask52 in
  let t3 = t3 +. (t2 >>. 52ul) in let t2 = t2 &. mask52 in
  let t4 = t4 +. (t3 >>. 52ul) in let t3 = t3 &. mask52 in
  (t0,t1,t2,t3,t4)


val lemma_a_mod_52_mul_b (a b:nat) :
  Lemma ((a % pow2 52) * pow2 b = a * pow2 b - a / pow2 52 * pow2 (b + 52))

let lemma_a_mod_52_mul_b a b =
  calc (==) {
    (a % pow2 52) * pow2 b;
    (==) { Math.Lemmas.euclidean_division_definition a (pow2 52) }
    (a - a / pow2 52 * pow2 52) * pow2 b;
    (==) { Math.Lemmas.distributivity_sub_left a (a / pow2 52 * pow2 52) (pow2 b) }
    a * pow2 b - a / pow2 52 * pow2 52 * pow2 b;
    (==) { Math.Lemmas.paren_mul_right (a / pow2 52) (pow2 52) (pow2 b); Math.Lemmas.pow2_plus 52 b }
    a * pow2 b - a / pow2 52 * pow2 (52 + b);
  }


val lemma_simplify_carry_round (t0 t1 t2 t3 t4:nat) : Lemma
 (let a = t1 + t0 / pow2 52 in
  let b = t2 + a / pow2 52 in
  let c = t3 + b / pow2 52 in
  let d = t4 + c / pow2 52 in
  t0 % pow2 52 + (a % pow2 52) * pow52 + (b % pow2 52) * pow104 +
  (c % pow2 52) * pow156 + d * pow208 ==
  t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208)

let lemma_simplify_carry_round t0 t1 t2 t3 t4 =
  let a = t1 + t0 / pow2 52 in
  let b = t2 + a / pow2 52 in
  let c = t3 + b / pow2 52 in
  let d = t4 + c / pow2 52 in

  calc (==) {
    t0 % pow2 52 + (a % pow2 52) * pow52 + (b % pow2 52) * pow104 + (c % pow2 52) * pow156 + d * pow208;
    (==) { lemma_a_mod_52_mul_b a 52 }
    t0 % pow2 52 + (t1 + t0 / pow2 52) * pow52 - a / pow52 * pow104 + (b % pow2 52) * pow104 + (c % pow2 52) * pow156 + d * pow208;
    (==) { Math.Lemmas.distributivity_add_left t1 (t0 / pow2 52) pow52; Math.Lemmas.euclidean_division_definition t0 (pow2 52) }
    t0 + t1 * pow52 - a / pow52 * pow104 + (b % pow2 52) * pow104 + (c % pow2 52) * pow156 + d * pow208;
    (==) { lemma_a_mod_52_mul_b b 104 }
    t0 + t1 * pow52 - a / pow52 * pow104 + (t2 + a / pow2 52) * pow104 - b / pow2 52 * pow156 + (c % pow2 52) * pow156 + d * pow208;
    (==) { Math.Lemmas.distributivity_add_left t2 (a / pow2 52) pow104 }
    t0 + t1 * pow52 + t2 * pow104 - b / pow2 52 * pow156 + (c % pow2 52) * pow156 + d * pow208;
    (==) { lemma_a_mod_52_mul_b c 156 }
    t0 + t1 * pow52 + t2 * pow104 - b / pow2 52 * pow156 + (t3 + b / pow2 52) * pow156 - c / pow2 52 * pow208 + d * pow208;
    (==) { Math.Lemmas.distributivity_add_left t3 (b / pow2 52) pow156 }
    t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 - c / pow2 52 * pow208 + (t4 + c / pow2 52) * pow208;
    (==) { Math.Lemmas.distributivity_add_left t4 (c / pow2 52) pow208 }
    t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208;
  }


val carry_round_after_last_carry_mod_prime5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m1 + 1 <= 4096 /\ m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\ m4 = 1 /\
    felem_fits5 f (m0,m1,m2,m3,1)))
  (ensures (let r = carry_round5 f in
    as_nat5 r == as_nat5 f /\ felem_fits5 r (1,1,1,1,2)))

let carry_round_after_last_carry_mod_prime5_lemma m f =
  let (m0,m1,m2,m3,m4) = m in
  let (t0,t1,t2,t3,t4) = f in //(m0,m1,m2,m3,1)

  let t1' = t1 +. (t0 >>. 52ul) in let t0' = t0 &. mask52 in
  lemma_carry52 m1 m0 t1 t0;
  assert (felem_fits1 t1' (m1 + 1));
  assert (felem_fits1 t0' 1);
  assert (v t0' = v t0 % pow2 52);
  assert (v t1' = v t1 + v t0 / pow2 52);

  let t2' = t2 +. (t1' >>. 52ul) in let t1'' = t1' &. mask52 in
  lemma_carry52 m2 (m1 + 1) t2 t1';
  assert (felem_fits1 t2' (m2 + 1));
  assert (felem_fits1 t1'' 1);
  assert (v t1'' = v t1' % pow2 52);
  assert (v t2' = v t2 + v t1' / pow2 52);

  let t3' = t3 +. (t2' >>. 52ul) in let t2'' = t2' &. mask52 in
  lemma_carry52 m3 (m2 + 1) t3 t2';
  assert (felem_fits1 t3' (m3 + 1));
  assert (felem_fits1 t2'' 1);
  assert (v t2'' = v t2' % pow2 52);
  assert (v t3' = v t3 + v t2' / pow2 52);

  let t4' = t4 +. (t3' >>. 52ul) in let t3'' = t3' &. mask52 in
  lemma_carry_last52 m4 (m3 + 1) t4 t3';
  assert (felem_fits_last1 t4' (m4 + 1));
  assert (felem_fits1 t3'' 1);
  assert (v t3'' = v t3' % pow2 52);
  assert (v t4' = v t4 + v t3' / pow2 52);

  lemma_simplify_carry_round (v t0) (v t1) (v t2) (v t3) (v t4);
  let r = carry_round5 f in
  assert ((t0',t1'',t2'',t3'',t4') == r);
  assert (as_nat5 r == as_nat5 f);
  assert (felem_fits5 r (1,1,1,1,2))


let normalize_weak5_lemma m f =
  let (m0,m1,m2,m3,m4) = m in

  let f1 = last_carry_mod_prime5 f in
  last_carry_mod_prime5_lemma m f;
  assert (as_nat5 f1 % S.prime = as_nat5 f % S.prime);
  assert (felem_fits5 f1 (m0+1,m1,m2,m3,1));

  let f2 = carry_round5 f1 in
  carry_round_after_last_carry_mod_prime5_lemma (m0+1,m1,m2,m3,1) f1;
  assert (as_nat5 f2 == as_nat5 f1);
  assert (felem_fits5 f2 (1,1,1,1,2));
  assert (f2 == normalize_weak5 f)
