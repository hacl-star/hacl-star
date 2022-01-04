module Hacl.Spec.K256.Field52.Lemmas1

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

///  Load and store functions

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


val lemma_a_mod_b_mul_c_mod_d (a b c d:nat) : Lemma
  (requires c <= d /\ b <= d - c)
  (ensures  (a % pow2 b) * pow2 c % pow2 d = (a % pow2 b) * pow2 c)

let lemma_a_mod_b_mul_c_mod_d a b c d =
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (a % pow2 b) d c;
  Math.Lemmas.pow2_modulo_modulo_lemma_2 a (d - c) b


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


val load_felem5_lemma_as_nat: s:felem4 -> f:felem5 -> Lemma
  (requires
   (let (s0,s1,s2,s3) = s in
    let (f0,f1,f2,f3,f4) = f in
    v f0 == v s0 % pow2 52 /\
    v f1 == v s0 / pow2 52 + v s1 % pow2 40 * pow2 12 /\
    v f2 == v s1 / pow2 40 + v s2 % pow2 28 * pow2 24 /\
    v f3 == v s2 / pow2 28 + v s3 % pow2 16 * pow2 36 /\
    v f4 == v s3 / pow2 16))
  (ensures as_nat5 f == as_nat4 s)

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


val load_felem5_lemma: s:felem4 ->
  Lemma (let f = load_felem5 s in
    felem_fits5 f (1,1,1,1,1) /\ as_nat5 f == as_nat4 s)

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


val store_felem5_lemma: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures  as_nat4 (store_felem5 f) == as_nat5 f)

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

val lemma_a_mul_c_plus_b_mul_c_mul_d (a b c d: nat) :
  Lemma (b * a + c * b * d == b * (a + c * d))

let lemma_a_mul_c_plus_b_mul_c_mul_d a b c d =
  Math.Lemmas.swap_mul c b;
  Math.Lemmas.paren_mul_right b c d;
  Math.Lemmas.distributivity_add_right b a (c * d)


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


val add5_lemma: m1:scale64_5 -> m2:scale64_5 -> f1:felem5 -> f2:felem5 -> Lemma
  (requires felem_fits5 f1 m1 /\ felem_fits5 f2 m2 /\ m1 +* m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = add5 f1 f2 in
    as_nat5 r == as_nat5 f1 + as_nat5 f2 /\ felem_fits5 r (m1 +* m2)))

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


val mul15_fits_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures  felem_fits5 (mul15 f c) (m1 ** mk_nat5 m2))

let mul15_fits_lemma m1 m2 f c =
  let (f0,f1,f2,f3,f4) = f in
  let (mf0,mf1,mf2,mf3,mf4) = m1 in
  let (r0,r1,r2,r3,r4) = mul15 f c in

  mul15_lemma1 mf0 m2 f0 c;
  assert (felem_fits1 r0 (mf0 * m2));
  mul15_lemma1 mf1 m2 f1 c;
  assert (felem_fits1 r1 (mf1 * m2));
  mul15_lemma1 mf2 m2 f2 c;
  assert (felem_fits1 r2 (mf2 * m2));
  mul15_lemma1 mf3 m2 f3 c;
  assert (felem_fits1 r3 (mf3 * m2));
  mul15_lemma_last1 mf4 m2 f4 c;
  assert (felem_fits_last1 r4 (mf4 * m2))


val mul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    as_nat5 r == v c * as_nat5 f /\ felem_fits5 r (m1 ** mk_nat5 m2)))

let mul15_lemma m1 m2 f c =
  let (f0,f1,f2,f3,f4) = f in
  let (mf0,mf1,mf2,mf3,mf4) = m1 in
  let (r0,r1,r2,r3,r4) = mul15 f c in
  mul15_fits_lemma m1 m2 f c;
  assert (felem_fits5 (r0,r1,r2,r3,r4) (m1 ** mk_nat5 m2));

  calc (==) { //as_nat5 (r0,r1,r2,r3,r4);
    v r0 + v r1 * pow52 + v r2 * pow104 + v r3 * pow156 + v r4 * pow208;
    (==) { mul15_lemma1 mf0 m2 f0 c }
    v f0 * v c + v r1 * pow52 + v r2 * pow104 + v r3 * pow156 + v r4 * pow208;
    (==) { mul15_lemma1 mf1 m2 f1 c }
    v f0 * v c + v f1 * v c * pow52 + v r2 * pow104 + v r3 * pow156 + v r4 * pow208;
    (==) { mul15_lemma1 mf2 m2 f2 c }
    v f0 * v c + v f1 * v c * pow52 + v f2 * v c * pow104 + v r3 * pow156 + v r4 * pow208;
    (==) { mul15_lemma1 mf3 m2 f3 c }
    v f0 * v c + v f1 * v c * pow52 + v f2 * v c * pow104 + v f3 * v c * pow156 + v r4 * pow208;
    (==) { mul15_lemma_last1 mf4 m2 f4 c; Math.Lemmas.swap_mul (v f0) (v c) }
    v c * v f0 + v f1 * v c * pow52 + v f2 * v c * pow104 + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0) (v c) (v f1) pow52 }
    v c * (v f0 + v f1 * pow52) + v f2 * v c * pow104 + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52) (v c) (v f2) pow104 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104) + v f3 * v c * pow156 + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52 + v f2 * pow104) (v c) (v f3) pow156 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156) + v f4 * v c * pow208;
    (==) { lemma_a_mul_c_plus_b_mul_c_mul_d (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156) (v c) (v f4) pow208 }
    v c * (v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208);
  };
  assert (as_nat5 (r0,r1,r2,r3,r4) == v c * as_nat5 f)
