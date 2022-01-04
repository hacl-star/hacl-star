module Hacl.Spec.K256.Field52.Lemmas2

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

///  Normalize-weak

val lemma_small_sub_mod: a:nat -> n:pos -> Lemma
  (requires n <= a /\ a < 2 * n)
  (ensures  a % n = a - n)

let lemma_small_sub_mod a n =
  calc (==) {
    a % n;
    (==) { Math.Lemmas.sub_div_mod_1 a n }
    (a - n) % n;
    (==) { Math.Lemmas.small_mod (a - n) n }
    a - n;
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


val minus_x_mul_pow2_256_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires felem_fits5 f m)
  (ensures
   (let x, r = minus_x_mul_pow2_256 f in
    let (r0,r1,r2,r3,r4) = r in
    let (m0,m1,m2,m3,m4) = m in
    let (t0,t1,t2,t3,t4) = f in
    v x < pow2 16 /\ v x = v t4 / pow2 48 /\
    v r4 = v t4 % pow2 48 /\
    as_nat5 r == as_nat5 f - v x * pow2 256 /\
    felem_fits5 r (m0,m1,m2,m3,1)))

let minus_x_mul_pow2_256_lemma m f =
  let (m0,m1,m2,m3,m4) = m in
  let (t0,t1,t2,t3,t4) = f in

  let x = t4 >>. 48ul in let t4' = t4 &. mask48 in
  assert_norm (v mask48 = pow2 48 - 1);
  mod_mask_lemma t4 48ul;
  assert (v (mod_mask #U64 #SEC 48ul) == v mask48);
  assert (v t4' = v t4 % pow2 48);
  assert (felem_fits_last1 t4' 1);

  let r = (t0,t1,t2,t3,t4') in
  calc (==) { // as_nat5 f
    v t0 + v t1 * pow52 + v t2 * pow104 + v t3 * pow156 + v t4 * pow208;
    (==) { Math.Lemmas.euclidean_division_definition (v t4) (pow2 48) }
    v t0 + v t1 * pow52 + v t2 * pow104 + v t3 * pow156 + (v t4 / pow2 48 * pow2 48 + v t4 % pow2 48) * pow208;
    (==) { Math.Lemmas.distributivity_add_left (v t4 / pow2 48 * pow2 48) (v t4 % pow2 48) pow208 }
    v t0 + v t1 * pow52 + v t2 * pow104 + v t3 * pow156 + (v t4 / pow2 48 * pow2 48) * pow208 + (v t4 % pow2 48) * pow208;
    (==) { }
    (v x * pow2 48) * pow208 + as_nat5 r;
    (==) { Math.Lemmas.paren_mul_right (v x) (pow2 48) pow208; Math.Lemmas.pow2_plus 48 208 }
    v x * pow2 256 + as_nat5 r;
  };

  Math.Lemmas.lemma_div_lt (v t4) 64 48


val lemma_carry52: m1:scale64 -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 4096)
  (ensures
    (let c = a +. (b >>. 52ul) in let d = b &. mask52 in
     felem_fits1 d 1 /\ felem_fits1 c (m1 + 1) /\
     v d = v b % pow2 52 /\ v c = v a + v b / pow2 52))

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
     v d = v b % pow2 52 /\ v c = v a + v b / pow2 52))

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


val carry_last_small_mod_lemma: t4:uint64 -> t3':uint64 -> Lemma
  (requires felem_fits_last1 t4 1 /\
    v (t4 +. (t3' >>. 52ul)) == v t4 + v t3' / pow2 52)
  (ensures  (let r = t4 +. (t3' >>. 52ul) in
    felem_fits_last1 r 2 /\
    v r < v t4 + pow2 12 /\ (v r >= pow2 48 ==> v r % pow2 48 < pow2 12)))

let carry_last_small_mod_lemma t4 t3' =
  let r = t4 +. (t3' >>. 52ul) in
  assert (v r = v t4 + v t3' / pow2 52);
  Math.Lemmas.lemma_div_lt (v t3') 64 52;
  assert (v r < pow2 48 - 1 + pow2 12);

  Math.Lemmas.pow2_lt_compat 48 12;
  assert (felem_fits_last1 r 2);

  if v r >= pow2 48 then begin
    lemma_small_sub_mod (v t4 + v t3' / pow2 52) (pow2 48);
    assert (v r % pow2 48 = v t4 + v t3' / pow2 52 - pow2 48);
    assert (v r % pow2 48 < pow2 12) end


val lemma_simplify_carry_round (t0 t1 t2 t3 t4:nat) : Lemma
 (let a = t1 + t0 / pow2 52 in
  let b = t2 + a / pow2 52 in
  let c = t3 + b / pow2 52 in
  let d = t4 + c / pow2 52 in
  t0 % pow2 52 + (a % pow2 52) * pow52 + (b % pow2 52) * pow104 + (c % pow2 52) * pow156 + d * pow208 ==
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
    let (r0,r1,r2,r3,r4) = r in
    let (t0,t1,t2,t3,t4) = f in
    as_nat5 r == as_nat5 f /\ felem_fits5 r (1,1,1,1,2) /\
    v r4 < v t4 + pow2 12 /\ (v r4 >= pow2 48 ==> v r4 % pow2 48 < pow2 12)))

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
  carry_last_small_mod_lemma t4 t3';

  lemma_simplify_carry_round (v t0) (v t1) (v t2) (v t3) (v t4);
  let r = carry_round5 f in
  assert ((t0',t1'',t2'',t3'',t4') == r);
  assert (as_nat5 r == as_nat5 f)


val plus_x_mul_pow2_256_minus_prime_lemma: m:scale64_5 -> x:uint64 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    let (t0,t1,t2,t3,t4) = f in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\ m4 = 1 /\
    felem_fits5 f m /\ v x < pow2 16))
  (ensures
   (let r = plus_x_mul_pow2_256_minus_prime x f in
    let (r0,r1,r2,r3,r4) = r in
    let (t0,t1,t2,t3,t4) = f in
    as_nat5 r == as_nat5 f + v x * (pow2 256 - S.prime) /\ felem_fits5 r (1,1,1,1,2) /\
    v r4 < v t4 + pow2 12 /\ (v r4 >= pow2 48 ==> v r4 % pow2 48 < pow2 12)))

let plus_x_mul_pow2_256_minus_prime_lemma m x f =
  let (t0,t1,t2,t3,t4) = f in
  let (m0,m1,m2,m3,m4) = m in

  let t0' = t0 +. x *. u64 0x1000003D1 in
  assert (v x < pow2 16);
  Math.Lemmas.lemma_mult_lt_right 0x1000003D1 (v x) (pow2 16);
  assert_norm (pow2 16 * 0x1000003D1 < max52);
  assert (v t0 + v x * 0x1000003D1 < (m0 + 1) * max52);
  Math.Lemmas.lemma_mult_le_right max52 (m0 + 1) 4096;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v t0 + v x * 0x1000003D1) (pow2 64);
  assert (v t0' = v t0 + v x * 0x1000003D1);
  assert (felem_fits1 t0' (m0 + 1));

  let r = carry_round5 (t0',t1,t2,t3,t4) in
  carry_round_after_last_carry_mod_prime5_lemma (m0+1,m1,m2,m3,m4) (t0',t1,t2,t3,t4);
  assert (as_nat5 r == as_nat5 (t0',t1,t2,t3,t4));
  LD.lemma_pow2_256_minus_prime ();
  assert (as_nat5 r == as_nat5 f + v x * (pow2 256 - S.prime))


val normalize_weak5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\
    felem_fits5 f m))
  (ensures (let r = normalize_weak5 f in
    let (r0,r1,r2,r3,r4) = r in
    let (t0,t1,t2,t3,t4) = f in
    as_nat5 r == as_nat5 f - v t4 / pow2 48 * S.prime /\ felem_fits5 r (1,1,1,1,2) /\
    v r4 < v t4 + pow2 12 /\ (v r4 >= pow2 48 ==> v r4 % pow2 48 < pow2 12)))

let normalize_weak5_lemma m f =
  let (m0,m1,m2,m3,m4) = m in

  let x, f1 = minus_x_mul_pow2_256 f in
  minus_x_mul_pow2_256_lemma m f;
  assert (as_nat5 f1 == as_nat5 f - v x * pow2 256);
  assert (felem_fits5 f1 (m0,m1,m2,m3,1));

  let f2 = plus_x_mul_pow2_256_minus_prime x f1 in
  plus_x_mul_pow2_256_minus_prime_lemma (m0,m1,m2,m3,1) x f1;
  assert (as_nat5 f2 == as_nat5 f1 + v x * (pow2 256 - S.prime));
  assert (felem_fits5 f2 (1,1,1,1,2));
  assert (f2 == normalize_weak5 f);
  Math.Lemmas.distributivity_sub_right (v x) (pow2 256) S.prime;
  assert (as_nat5 f2 == as_nat5 f - v x * S.prime)


///  Normalize

#push-options "--ifuel 1"
val is_felem_ge_prime5_lemma: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures  (let is_m = is_felem_ge_prime5 f in
    (v is_m = 0 \/ v is_m = ones_v U64) /\
    (if v is_m = ones_v U64 then (as_nat5 f >= S.prime) else (as_nat5 f < S.prime))))

let is_felem_ge_prime5_lemma f = ()
#pop-options
  // let (f0,f1,f2,f3,f4) = f in
  // let m4 = eq_mask f4 mask48 in
  // eq_mask_lemma f4 mask48;
  // assert (if v f4 = v mask48 then v m4 = ones_v U64 else v m4 = 0);

  // let m3 = eq_mask f3 mask52 in
  // eq_mask_lemma f3 mask52;
  // assert (if v f3 = v mask52 then v m3 = ones_v U64 else v m3 = 0);

  // let m2 = eq_mask f2 mask52 in
  // eq_mask_lemma f2 mask52;
  // assert (if v f2 = v mask52 then v m2 = ones_v U64 else v m2 = 0);

  // let m1 = eq_mask f1 mask52 in
  // eq_mask_lemma f1 mask52;
  // assert (if v f1 = v mask52 then v m1 = ones_v U64 else v m1 = 0);

  // let m0 = gte_mask f0 (u64 0xffffefffffc2f) in
  // gte_mask_lemma f0 (u64 0xffffefffffc2f);
  // assert (if v f0 >= 0xffffefffffc2f then v m0 = ones_v U64 else v m0 = 0);

  // let m = m0 &. m1 &. m2 &. m3 &. m4 in ()
  // if v m4 = 0 then
  //   logand_zeros (m0 &. m1 &. m2 &. m3)
  // else begin
  //   logand_ones (m0 &. m1 &. m2 &. m3) end


noextract
let normalize5_first_part (f0,f1,f2,f3,f4) =
  let (t0,t1,t2,t3,t4) = normalize_weak5 (f0,f1,f2,f3,f4) in
  let x, (r0,r1,r2,r3,r4) = minus_x_mul_pow2_256 (t0,t1,t2,t3,t4) in
  x, (r0,r1,r2,r3,r4)

noextract
let normalize5_second_part_x (x:uint64) (r0,r1,r2,r3,r4) : felem5 =
  let is_ge_p_m = is_felem_ge_prime5 (r0,r1,r2,r3,r4) in // as_nat r >= S.prime
  let m_to_one = is_ge_p_m &. u64 1 in
  let x1 = m_to_one |. x in
  let (s0,s1,s2,s3,s4) = plus_x_mul_pow2_256_minus_prime x1 (r0,r1,r2,r3,r4) in
  let x2, (k0,k1,k2,k3,k4) = minus_x_mul_pow2_256 (s0,s1,s2,s3,s4) in
  (k0,k1,k2,k3,k4)


val normalize5_first_part_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\
    felem_fits5 f m))
  (ensures (let x, r = normalize5_first_part f in
    let (f0,f1,f2,f3,f4) = f in
    let (r0,r1,r2,r3,r4) = r in
    as_nat5 r == as_nat5 f - v f4 / pow2 48 * S.prime - v x * pow2 256 /\
    felem_fits5 r (1,1,1,1,1) /\ (v x = 0 \/ (v x = 1 /\ v r4 < pow2 12))))

let normalize5_first_part_lemma m f =
  let (m0,m1,m2,m3,m4) = m in
  let (f0,f1,f2,f3,f4) = f in
  let t = normalize_weak5 f in
  let (t0,t1,t2,t3,t4) = t in
  normalize_weak5_lemma m f;
  assert (as_nat5 t == as_nat5 f - v f4 / pow2 48 * S.prime);
  assert (felem_fits5 t (1,1,1,1,2));
  assert ((v t4 >= pow2 48 ==> v t4 % pow2 48 < pow2 12));

  let x, r = minus_x_mul_pow2_256 t in
  let (r0,r1,r2,r3,r4) = r in
  minus_x_mul_pow2_256_lemma (1,1,1,1,2) t;
  assert (as_nat5 r == as_nat5 t - v x * pow2 256);
  assert (as_nat5 r == as_nat5 f - v f4 / pow2 48 * S.prime - v x * pow2 256);
  assert (felem_fits5 r (1,1,1,1,1));
  assert (v r4 = v t4 % pow2 48 /\ v x = v t4 / pow2 48);
  LD.lemma_div_pow48 t4;
  assert (if v t4 < pow2 48 then v x = 0 else v x = 1 /\ v r4 < pow2 12)


val normalize5_second_part_x_is_one_lemma: x:uint64 -> r:felem5 -> Lemma
  (requires (let (r0,r1,r2,r3,r4) = r in
    felem_fits5 r (1,1,1,1,1) /\ v x = 1 /\ v r4 < pow2 12))
  (ensures (let k = normalize5_second_part_x x r in
    as_nat5 k == as_nat5 r + v x * pow2 256 - S.prime /\
    felem_fits5 k (1,1,1,1,1) /\ as_nat5 k < S.prime))

let normalize5_second_part_x_is_one_lemma x r =
  LD.lemma_as_nat_bound_f4_lt_pow12 r;
  assert (as_nat5 r <= pow2 220 - 1);
  assert_norm (pow2 220 - 1 < S.prime);

  let is_ge_p_m = is_felem_ge_prime5 r in
  is_felem_ge_prime5_lemma r;
  assert (v is_ge_p_m = 0);

  let m_to_one = is_ge_p_m &. u64 1 in
  logand_lemma is_ge_p_m (u64 1);
  assert (v m_to_one = 0);

  let x1 = m_to_one |. x in //1
  logor_spec m_to_one x;
  FStar.UInt.logor_commutative #64 (v m_to_one) (v x);
  FStar.UInt.logor_lemma_1 #64 (v x);
  assert (v x1 = 1);

  let s = plus_x_mul_pow2_256_minus_prime x1 r in // + x * (pow2 256 - S.prime)
  plus_x_mul_pow2_256_minus_prime_lemma (1,1,1,1,1) x1 r;
  assert (as_nat5 s = as_nat5 r + pow2 256 - S.prime); //(v s4 >= pow2 48 ==> v s4 % pow2 48 < pow2 12)

  let (s0,s1,s2,s3,s4) = s in
  Math.Lemmas.pow2_double_sum 12;
  assert (v s4 < pow2 13);

  let x2, k = minus_x_mul_pow2_256 s in // - s4 / pow2 48 * pow2 256
  minus_x_mul_pow2_256_lemma (1,1,1,1,2) s;
  assert (felem_fits5 k (1,1,1,1,1));
  assert (as_nat5 k = as_nat5 s - v s4 / pow2 48 * pow2 256);

  LD.lemma_div_pow48 s4;
  assert (as_nat5 k = as_nat5 s);
  assert (as_nat5 k < pow2 220 + pow2 256 - S.prime);
  assert_norm (pow2 220 + pow2 256 - S.prime < S.prime)


val normalize5_second_part_x_is_zero_lemma: x:uint64 -> r:felem5 -> Lemma
  (requires (let (r0,r1,r2,r3,r4) = r in
    felem_fits5 r (1,1,1,1,1) /\ v x = 0))
  (ensures (let k = normalize5_second_part_x x r in
    as_nat5 k == (if as_nat5 r < S.prime then as_nat5 r else as_nat5 r - S.prime) /\
    felem_fits5 k (1,1,1,1,1) /\ as_nat5 k < S.prime))

let normalize5_second_part_x_is_zero_lemma x r =
  let is_ge_p_m = is_felem_ge_prime5 r in
  is_felem_ge_prime5_lemma r;
  assert (if v is_ge_p_m = ones_v U64
    then (as_nat5 r >= S.prime) else as_nat5 r < S.prime);

  let m_to_one = is_ge_p_m &. u64 1 in
  logand_lemma is_ge_p_m (u64 1);
  assert (if v is_ge_p_m = ones_v U64 then v m_to_one = 1 else v m_to_one = 0);

  let x1 = m_to_one |. x in //1
  logor_spec m_to_one x;
  FStar.UInt.logor_lemma_1 #64 (v m_to_one);
  assert (v x1 = v m_to_one);

  assert (if v x1 = 1 then (as_nat5 r >= S.prime) else as_nat5 r < S.prime);

  let s = plus_x_mul_pow2_256_minus_prime x1 r in // + x1 * (pow2 256 - S.prime)
  plus_x_mul_pow2_256_minus_prime_lemma (1,1,1,1,1) x1 r;
  assert (as_nat5 s = as_nat5 r + v x1 * (pow2 256 - S.prime)); //(v s4 >= pow2 48 ==> v s4 % pow2 48 < pow2 12)

  let (s0,s1,s2,s3,s4) = s in
  let x2, k = minus_x_mul_pow2_256 s in // - s4 / pow2 48 * pow2 256
  minus_x_mul_pow2_256_lemma (1,1,1,1,2) s;
  assert (felem_fits5 k (1,1,1,1,1));
  assert (as_nat5 k = as_nat5 s - v s4 / pow2 48 * pow2 256);

  if v x1 = 0 then begin
    assert (as_nat5 s = as_nat5 r);
    LD.as_nat_inj s r;
    assert (felem_fits_last1 s4 1);
    Math.Lemmas.small_div (v s4) (pow2 48);
    assert (as_nat5 k = as_nat5 r) end
  else begin
    assert (as_nat5 s = as_nat5 r + pow2 256 - S.prime);
    assert (as_nat5 s >= pow2 256);
    assert (v s4 >= pow2 48);
    LD.lemma_div_pow48 s4;
    assert (as_nat5 k = as_nat5 r - S.prime) end


val lemma_a_minus_b_prime_c_prime_k (k a b c:nat) (n:pos) : Lemma
  (requires k < n /\ k == a - b * n - c * n)
  (ensures  k == a % n)

let lemma_a_minus_b_prime_c_prime_k k a b c n =
  Math.Lemmas.lemma_mod_sub (a - b * n) n c;
  Math.Lemmas.lemma_mod_sub a n b;
  Math.Lemmas.small_mod k n


val normalize5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\
    felem_fits5 f m))
  (ensures (let r = normalize5 f in
    as_nat5 r == as_nat5 f % S.prime  /\
    felem_fits5 r (1,1,1,1,1)))

let normalize5_lemma m f =
  let (m0,m1,m2,m3,m4) = m in
  let (f0,f1,f2,f3,f4) = f in
  let x, r = normalize5_first_part f in
  let k = normalize5_second_part_x x r in

  let (r0,r1,r2,r3,r4) = r in
  normalize5_first_part_lemma m f;
  assert (as_nat5 r == as_nat5 f - v f4 / pow2 48 * S.prime - v x * pow2 256);

  if v x = 1 then begin
    normalize5_second_part_x_is_one_lemma x r;
    lemma_a_minus_b_prime_c_prime_k (as_nat5 k) (as_nat5 f) (v f4 / pow2 48) 1 S.prime end
  else begin
    normalize5_second_part_x_is_zero_lemma x r;
    if as_nat5 r < S.prime then
      lemma_a_minus_b_prime_c_prime_k (as_nat5 k) (as_nat5 f) (v f4 / pow2 48) 0 S.prime
    else
      lemma_a_minus_b_prime_c_prime_k (as_nat5 k) (as_nat5 f) (v f4 / pow2 48) 1 S.prime end
