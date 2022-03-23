module Hacl.Spec.K256.MathLemmas

open FStar.Mul

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_swap_mul3 (a b c:int) : Lemma (a * b * c == a * c * b)
let lemma_swap_mul3 a b c =
  calc (==) {
    a * b * c;
    (==) { Math.Lemmas.paren_mul_right a b c }
    a * (b * c);
    (==) { Math.Lemmas.swap_mul b c }
    a * (c * b);
    (==) { Math.Lemmas.paren_mul_right a c b }
    a * c * b;
  }


val lemma_mod_mul_distr (a b:int) (n:pos) : Lemma (a * b % n = (a % n) * (b % n) % n)
let lemma_mod_mul_distr a b n =
  Math.Lemmas.lemma_mod_mul_distr_l a b n;
  Math.Lemmas.lemma_mod_mul_distr_r (a % n) b n


val lemma_mod_sub_distr (a b:int) (n:pos) : Lemma ((a - b) % n = (a % n - b % n) % n)
let lemma_mod_sub_distr a b n =
  Math.Lemmas.lemma_mod_plus_distr_l a (- b) n;
  Math.Lemmas.lemma_mod_sub_distr (a % n) b n


val lemma_ab_le_cd (a b c d:nat) : Lemma
  (requires a <= c /\ b <= d)
  (ensures a * b <= c * d)
let lemma_ab_le_cd a b c d =
  Math.Lemmas.lemma_mult_le_left a b d;
  Math.Lemmas.lemma_mult_le_right d a c


val lemma_ab_lt_cd (a b c d:pos) : Lemma
  (requires a < c /\ b < d)
  (ensures a * b < c * d)
let lemma_ab_lt_cd a b c d =
  Math.Lemmas.lemma_mult_lt_left a b d;
  Math.Lemmas.lemma_mult_lt_right d a c


val lemma_bound_mul64_wide (ma mb:nat) (mma mmb:nat) (a b:nat) : Lemma
  (requires a <= ma * mma /\ b <= mb * mmb)
  (ensures  a * b <= ma * mb * (mma * mmb))

let lemma_bound_mul64_wide ma mb mma mmb a b =
  calc (<=) {
    a * b;
    (<=) { lemma_ab_le_cd a b (ma * mma) (mb * mmb) }
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


val lemma_distr_pow (a b:int) (c d:nat) : Lemma ((a + b * pow2 c) * pow2 d = a * pow2 d + b * pow2 (c + d))
let lemma_distr_pow a b c d =
  calc (==) {
    (a + b * pow2 c) * pow2 d;
    (==) { Math.Lemmas.distributivity_add_left a (b * pow2 c) (pow2 d) }
    a * pow2 d + b * pow2 c * pow2 d;
    (==) { Math.Lemmas.paren_mul_right b (pow2 c) (pow2 d); Math.Lemmas.pow2_plus c d }
    a * pow2 d + b * pow2 (c + d);
  }


val lemma_distr_pow_pow (a:int) (b:nat) (c:int) (d e:nat) :
  Lemma ((a * pow2 b + c * pow2 d) * pow2 e = a * pow2 (b + e) + c * pow2 (d + e))
let lemma_distr_pow_pow a b c d e =
  calc (==) {
    (a * pow2 b + c * pow2 d) * pow2 e;
    (==) { lemma_distr_pow (a * pow2 b) c d e }
    a * pow2 b * pow2 e + c * pow2 (d + e);
    (==) { Math.Lemmas.paren_mul_right a (pow2 b) (pow2 e); Math.Lemmas.pow2_plus b e }
    a * pow2 (b + e) + c * pow2 (d + e);
  }


val lemma_distr_eucl_mul (r a:int) (b:pos) : Lemma (r * (a % b) + r * (a / b) * b = r * a)
let lemma_distr_eucl_mul r a b =
  calc (==) {
    r * (a % b) + r * (a / b) * b;
    (==) { Math.Lemmas.paren_mul_right r (a / b) b }
    r * (a % b) + r * ((a / b) * b);
    (==) { Math.Lemmas.distributivity_add_right r (a % b) (a / b * b) }
    r * (a % b + a / b * b);
    (==) { Math.Lemmas.euclidean_division_definition a b }
    r * a;
  }


val lemma_distr_eucl_mul_add (r a c:int) (b:pos) : Lemma (r * (a % b) + r * (a / b + c) * b = r * a + r * c * b)
let lemma_distr_eucl_mul_add r a c b =
  calc (==) {
    r * (a % b) + r * (a / b + c) * b;
    (==) { Math.Lemmas.paren_mul_right r (a / b + c) b }
    r * (a % b) + r * ((a / b + c) * b);
    (==) { Math.Lemmas.distributivity_add_left (a / b) c b }
    r * (a % b) + r * ((a / b * b) + c * b);
    (==) { Math.Lemmas.distributivity_add_right r (a / b * b) (c * b) }
    r * (a % b) + r * (a / b * b) + r * (c * b);
    (==) { Math.Lemmas.paren_mul_right r (a / b) b; Math.Lemmas.paren_mul_right r c b }
    r * (a % b) + r * (a / b) * b + r * c * b;
    (==) { lemma_distr_eucl_mul r a b }
    r * a + r * c * b;
  }


val lemma_distr_eucl (a b:int) : Lemma ((a / pow2 52 + b) * pow2 52 + a % pow2 52 = a + b * pow2 52)
let lemma_distr_eucl a b = lemma_distr_eucl_mul_add 1 a b (pow2 52)


val lemma_a_plus_b_pow2_mod2 (a b:int) (c:pos) : Lemma ((a + b * pow2 c) % 2 = a % 2)
let lemma_a_plus_b_pow2_mod2 a b c =
  assert_norm (pow2 1 = 2);
  Math.Lemmas.lemma_mod_plus_distr_r a (b * pow2 c) 2;
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 b 1 c


val lemma_as_nat64_horner (r0 r1 r2 r3:int) :
  Lemma (r0 + r1 * pow2 64 + r2 * pow2 128 + r3 * pow2 192 ==
    ((r3 * pow2 64 + r2) * pow2 64 + r1) * pow2 64 + r0)

let lemma_as_nat64_horner r0 r1 r2 r3 =
  calc (==) {
    r0 + pow2 64 * (r1 + pow2 64 * (r2 + pow2 64 * r3));
    (==) { Math.Lemmas.swap_mul (pow2 64) (r1 + pow2 64 * (r2 + pow2 64 * r3)) }
    r0 + (r1 + pow2 64 * (r2 + pow2 64 * r3)) * pow2 64;
    (==) { Math.Lemmas.swap_mul (pow2 64) (r2 + pow2 64 * r3) }
    r0 + (r1 + (r2 + pow2 64 * r3) * pow2 64) * pow2 64;
    (==) { lemma_distr_pow r1 (r2 + pow2 64 * r3) 64 64 }
    r0 + r1 * pow2 64 + (r2 + pow2 64 * r3) * pow2 128;
    (==) { Math.Lemmas.swap_mul (pow2 64) r3 }
    r0 + r1 * pow2 64 + (r2 + r3 * pow2 64) * pow2 128;
    (==) { lemma_distr_pow r2 r3 64 128 }
    r0 + r1 * pow2 64 + r2 * pow2 128 + r3 * pow2 192;
  }


val lemma_as_nat_horner (r0 r1 r2 r3 r4:int) :
  Lemma (r0 + r1 * pow2 52 + r2 * pow2 104 + r3 * pow2 156 + r4 * pow2 208 ==
    (((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0)

let lemma_as_nat_horner r0 r1 r2 r3 r4 =
  calc (==) {
    (((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 52 + r1) * pow2 52 + r0;
    (==) { lemma_distr_pow r1 ((r4 * pow2 52 + r3) * pow2 52 + r2) 52 52 }
    ((r4 * pow2 52 + r3) * pow2 52 + r2) * pow2 104 + r1 * pow2 52 + r0;
    (==) { lemma_distr_pow r2 (r4 * pow2 52 + r3) 52 104 }
    (r4 * pow2 52 + r3) * pow2 156 + r2 * pow2 104 + r1 * pow2 52 + r0;
    (==) { lemma_distr_pow r3 r4 52 156 }
    r4 * pow2 208 + r3 * pow2 156 + r2 * pow2 104 + r1 * pow2 52 + r0;
  }


val lemma_distr5 (a0 a1 a2 a3 a4 b:int) : Lemma
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
    (==) { Math.Lemmas.distributivity_add_left a3 a4 b }
    a0 * b + a1 * b + a2 * b + a3 * b + a4 * b;
  }


val lemma_distr5_pow52 (a b0 b1 b2 b3 b4:int) : Lemma
  (a * (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) =
   a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156 + a * b4 * pow2 208)

let lemma_distr5_pow52 a b0 b1 b2 b3 b4 =
  calc (==) {
    a * (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208);
    (==) { lemma_distr5 b0 (b1 * pow2 52) (b2 * pow2 104) (b3 * pow2 156) (b4 * pow2 208) a }
    b0 * a + b1 * pow2 52 * a + b2 * pow2 104 * a + b3 * pow2 156 * a + b4 * pow2 208 * a;
    (==) { lemma_swap_mul3 b1 (pow2 52) a; lemma_swap_mul3 b2 (pow2 104) a }
    b0 * a + b1 * a * pow2 52 + b2 * a * pow2 104 + b3 * pow2 156 * a + b4 * pow2 208 * a;
    (==) { lemma_swap_mul3 b3 (pow2 156) a; lemma_swap_mul3 b4 (pow2 208) a }
    b0 * a + b1 * a * pow2 52 + b2 * a * pow2 104 + b3 * a * pow2 156 + b4 * a * pow2 208;
  }


val lemma_distr5_pow52_mul_pow (a b0 b1 b2 b3 b4: int) (p:nat) : Lemma
  (a * pow2 p * (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) =
   a * b0 * pow2 p + a * b1 * pow2 (52 + p) + a * b2 * pow2 (104 + p) +
   a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p))

let lemma_distr5_pow52_mul_pow a b0 b1 b2 b3 b4 p =
  let b_sum = b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208 in
  calc (==) {
    a * pow2 p * b_sum;
    (==) { lemma_swap_mul3 a (pow2 p) b_sum }
    a * b_sum * pow2 p;
    (==) { lemma_distr5_pow52 a b0 b1 b2 b3 b4 }
    (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156 + a * b4 * pow2 208) * pow2 p;
    (==) { lemma_distr_pow (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156) (a * b4) 208 p }
    (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104 + a * b3 * pow2 156) * pow2 p + a * b4 * pow2 (208 + p);
    (==) { lemma_distr_pow (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104) (a * b3) 156 p }
    (a * b0 + a * b1 * pow2 52 + a * b2 * pow2 104) * pow2 p + a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p);
    (==) { lemma_distr_pow (a * b0 + a * b1 * pow2 52) (a * b2) 104 p }
    (a * b0 + a * b1 * pow2 52) * pow2 p + a * b2 * pow2 (104 + p) + a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p);
    (==) { lemma_distr_pow (a * b0) (a * b1) 52 p }
    a * b0 * pow2 p + a * b1 * pow2 (52 + p) + a * b2 * pow2 (104 + p) + a * b3 * pow2 (156 + p) + a * b4 * pow2 (208 + p);
  }


val lemma_distr5_pow52_sub (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c:int) : Lemma
  ((b0 * c - a0) + (b1 * c - a1) * pow2 52 + (b2 * c - a2) * pow2 104 +
   (b3 * c - a3) * pow2 156 + (b4 * c - a4) * pow2 208 ==
   (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) * c -
   (a0 + a1 * pow2 52 + a2 * pow2 104 + a3 * pow2 156 + a4 * pow2 208))

let lemma_distr5_pow52_sub a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c =
  calc (==) {
    (b0 * c - a0) + (b1 * c - a1) * pow2 52 + (b2 * c - a2) * pow2 104 +
    (b3 * c - a3) * pow2 156 + (b4 * c - a4) * pow2 208;
    (==) { Math.Lemmas.distributivity_sub_left (b1 * c) a1 (pow2 52) }
    c * b0 - a0 + c * b1 * pow2 52 - a1 * pow2 52 + (b2 * c - a2) * pow2 104 +
    (b3 * c - a3) * pow2 156 + (b4 * c - a4) * pow2 208;
    (==) { Math.Lemmas.distributivity_sub_left (b2 * c) a2 (pow2 104) }
    c * b0 - a0 + c * b1 * pow2 52 - a1 * pow2 52 + c * b2 * pow2 104 - a2 * pow2 104 +
    (b3 * c - a3) * pow2 156 + (b4 * c - a4) * pow2 208;
    (==) { Math.Lemmas.distributivity_sub_left (b3 * c) a3 (pow2 156) }
    c * b0 - a0 + c * b1 * pow2 52 - a1 * pow2 52 + c * b2 * pow2 104 - a2 * pow2 104 +
    c * b3 * pow2 156 - a3 * pow2 156 + (b4 * c - a4) * pow2 208;
    (==) { Math.Lemmas.distributivity_sub_left (b4 * c) a4 (pow2 208) }
    c * b0 - a0 + c * b1 * pow2 52 - a1 * pow2 52 + c * b2 * pow2 104 - a2 * pow2 104 +
    c * b3 * pow2 156 - a3 * pow2 156 + c * b4 * pow2 208 - a4 * pow2 208;
    (==) { lemma_distr5_pow52 c b0 b1 b2 b3 b4 }
    (b0 + b1 * pow2 52 + b2 * pow2 104 + b3 * pow2 156 + b4 * pow2 208) * c -
    (a0 + a1 * pow2 52 + a2 * pow2 104 + a3 * pow2 156 + a4 * pow2 208);
  }


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
    (==) { lemma_distr_pow (a / pow2 b) d f g }
    a % pow2 b * pow2 c + (a / pow2 b) * pow2 (c + b) + d * pow2 (f + g);
    (==) { lemma_distr_pow (a % pow2 b) (a / pow2 b) b c }
    (a % pow2 b + (a / pow2 b) * pow2 b) * pow2 c + d * pow2 (f + g);
    (==) { Math.Lemmas.euclidean_division_definition a (pow2 b) }
    a * pow2 c + d * pow2 (f + g);
  }


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
  t0 % pow2 52 + (a % pow2 52) * pow2 52 + (b % pow2 52) * pow2 104 +
  (c % pow2 52) * pow2 156 + d * pow2 208 ==
  t0 + t1 * pow2 52 + t2 * pow2 104 + t3 * pow2 156 + t4 * pow2 208)

let lemma_simplify_carry_round t0 t1 t2 t3 t4 =
  let a = t1 + t0 / pow2 52 in
  let b = t2 + a / pow2 52 in
  let c = t3 + b / pow2 52 in
  let d = t4 + c / pow2 52 in

  calc (==) {
    t0 % pow2 52 + (a % pow2 52) * pow2 52 + (b % pow2 52) * pow2 104 +
    (c % pow2 52) * pow2 156 + d * pow2 208;
    (==) { lemma_a_mod_52_mul_b a 52 }
    t0 % pow2 52 + (t1 + t0 / pow2 52) * pow2 52 - a / pow2 52 * pow2 104 + (b % pow2 52) * pow2 104 +
    (c % pow2 52) * pow2 156 + d * pow2 208;
    (==) { lemma_distr_eucl t0 t1 }
    t0 + t1 * pow2 52 - a / pow2 52 * pow2 104 + (b % pow2 52) * pow2 104 +
    (c % pow2 52) * pow2 156 + d * pow2 208;
    (==) { lemma_a_mod_52_mul_b b 104 }
    t0 + t1 * pow2 52 - a / pow2 52 * pow2 104 + (t2 + a / pow2 52) * pow2 104 - b / pow2 52 * pow2 156 +
    (c % pow2 52) * pow2 156 + d * pow2 208;
    (==) { Math.Lemmas.distributivity_add_left t2 (a / pow2 52) (pow2 104) }
    t0 + t1 * pow2 52 + t2 * pow2 104 - b / pow2 52 * pow2 156 +
    (c % pow2 52) * pow2 156 + d * pow2 208;
    (==) { lemma_a_mod_52_mul_b c 156 }
    t0 + t1 * pow2 52 + t2 * pow2 104 - b / pow2 52 * pow2 156 +
    (t3 + b / pow2 52) * pow2 156 - c / pow2 52 * pow2 208 + d * pow2 208;
    (==) { Math.Lemmas.distributivity_add_left t3 (b / pow2 52) (pow2 156) }
    t0 + t1 * pow2 52 + t2 * pow2 104 + t3 * pow2 156 - c / pow2 52 * pow2 208 + (t4 + c / pow2 52) * pow2 208;
    (==) { Math.Lemmas.distributivity_add_left t4 (c / pow2 52) (pow2 208) }
    t0 + t1 * pow2 52 + t2 * pow2 104 + t3 * pow2 156 + t4 * pow2 208;
  }
