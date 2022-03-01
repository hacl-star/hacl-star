module Hacl.Spec.K256.Field52.Lemmas

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas
module L1 = Hacl.Spec.K256.Field52.Lemmas1
module L2 = Hacl.Spec.K256.Field52.Lemmas2
module L3 = Hacl.Spec.K256.Field52.Lemmas3
module L4 = Hacl.Spec.K256.Field52.Lemmas4

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let load_felem5_lemma s =
  L1.load_felem5_lemma s


let store_felem5_lemma f =
  L1.store_felem5_lemma f


let add5_lemma m1 m2 f1 f2 =
  L1.add5_lemma m1 m2 f1 f2


let fadd5_lemma m1 m2 f1 f2 =
  let r = add5 f1 f2 in
  add5_lemma m1 m2 f1 f2;
  assert (as_nat5 r == as_nat5 f1 + as_nat5 f2);
  Math.Lemmas.modulo_distributivity (as_nat5 f1) (as_nat5 f2) S.prime


let mul15_lemma m1 m2 f c =
  L1.mul15_lemma m1 m2 f c


let fmul15_lemma m1 m2 f c =
  let r = mul15 f c in
  mul15_lemma m1 m2 f c;
  assert (as_nat5 r == v c * as_nat5 f);
  Math.Lemmas.lemma_mod_mul_distr_r (v c) (as_nat5 f) S.prime


#push-options "--ifuel 1"
let is_felem_zero_vartime5_lemma f = ()


let is_felem_ge_prime_vartime5_lemma f =
  let p =
   (u64 0xffffefffffc2f,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xffffffffffff) in
  assert_norm (S.prime = as_nat5 p);
  assert_norm (0xffffefffffc2f <= max52);
  assert_norm (0xfffffffffffff = max52);
  assert_norm (0xffffffffffff = max48);
  assert (felem_fits5 p (1,1,1,1,1));
  //LD.lemma_as_nat_decompose f;
  //LD.lemma_as_nat_decompose p;
  LD.lemma_as_nat_bound f;
  LD.lemma_as_nat_bound p


let is_felem_lt_prime_minus_order_vartime5_lemma f =
  assert_norm (S.prime - S.q =
    0xda1722fc9baee + 0x1950b75fc4402 * pow52 + 0x1455123 * pow104)


let is_felem_eq_vartime5_lemma f1 f2 =
  if as_nat5 f1 = as_nat5 f2 then LD.as_nat_inj f1 f2
#pop-options


let normalize_weak5_lemma m f =
  let r = normalize_weak5 f in
  let (r0,r1,r2,r3,r4) = r in
  let (t0,t1,t2,t3,t4) = f in
  L2.normalize_weak5_lemma m f;
  assert (as_nat5 r == as_nat5 f - v t4 / pow2 48 * S.prime);
  Math.Lemmas.lemma_mod_sub (as_nat5 f) S.prime (v t4 / pow2 48)


let normalize5_lemma m f =
  L2.normalize5_lemma m f


let fmul5_lemma a b =
  L3.fmul5_lemma a b

let fmul5_lemma1 a b =
  let r = fmul5 a b in
  L3.fmul5_lemma a b;
  assert (as_nat5 r % S.prime == as_nat5 a * as_nat5 b % S.prime);
  Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 a) (as_nat5 b) S.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (feval5 a) (as_nat5 b) S.prime


let fsqr5_lemma a =
  L3.fsqr5_lemma a

let fsqr5_lemma1 a =
  let r = fsqr5 a in
  L3.fsqr5_lemma a;
  assert (as_nat5 r % S.prime == as_nat5 a * as_nat5 a % S.prime);
  Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 a) (as_nat5 a) S.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (feval5 a) (as_nat5 a) S.prime


val lemma_mul_sub (mc:nat) (a b c:uint64) : Lemma
  (requires
    v a <= max52 /\ max52 <= v a * 2 /\ v c <= mc * max52 /\
    mc <= v b /\ 2 * v b <= 4096)
  (ensures (let r = a *. u64 2 *. b -. c in
    v r = v a * 2 * v b - v c /\
    felem_fits1 r (2 * v b)))

let lemma_mul_sub mc a b c =
  let r = a *. u64 2 *. b -. c in
  assert (v c <= mc * max52);
  Math.Lemmas.lemma_mult_le_left mc max52 (v a * 2);
  Math.Lemmas.lemma_mult_le_right (v a * 2) mc (v b);
  assert (mc * max52 <= v b * (v a * 2));
  assert (v c <= v a * 2 * v b);

  Math.Lemmas.paren_mul_right (v a) 2 (v b);
  Math.Lemmas.lemma_mult_le_right (2 * v b) (v a) max52;
  assert (v a * 2 * v b - v c <= max52 * (2 * v b));
  Math.Lemmas.lemma_mult_le_left max52 (2 * v b) 4096;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a * 2 * v b - v c) (pow2 64);
  assert (v r = v a * 2 * v b - v c);
  assert (felem_fits1 r (2 * v b))


val lemma_ab_lt_cd (a b c d:nat) : Lemma
  (requires a <= c /\ b <= d)
  (ensures a * b <= c * d)

let lemma_ab_lt_cd a b c d =
  Math.Lemmas.lemma_mult_le_left a b d;
  Math.Lemmas.lemma_mult_le_right d a c


val lemma_mul_sub_last (mc:nat) (a b c:uint64) : Lemma
  (requires
    v a <= max48 /\ max48 <= v a * 2 /\ v c <= mc * max48 /\
    mc <= v b /\ 2 * v b <= 65536)
  (ensures (let r = a *. u64 2 *. b -. c in
    v r = v a * 2 * v b - v c /\
    felem_fits_last1 r (2 * v b)))

let lemma_mul_sub_last mc a b c =
  let r = a *. u64 2 *. b -. c in

  assert (v c <= mc * max48);
  lemma_ab_lt_cd mc max48 (v b) (v a * 2);
  assert (v c <= v b * (v a * 2));

  assert (v a * 2 * v b - v c <= v a * 2 * v b);
  Math.Lemmas.paren_mul_right (v a) 2 (v b);
  lemma_ab_lt_cd (v a) (2 * v b) max48 65536;
  assert_norm (65536 * max48 < pow2 64);
  Math.Lemmas.small_mod (v a * 2 * v b - v c) (pow2 64);
  assert (v r = v a * 2 * v b - v c);

  lemma_ab_lt_cd (v a) (2 * v b) max48 (2 * v b);
  assert (felem_fits_last1 r (2 * v b))


val fnegate5_lemma (m:scale64_5) (a:felem5) (x:uint64) : Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in 2 * v x <= 4096 /\
    m0 <= v x /\ m1 <= v x /\ m2 <= v x /\ m3 <= v x /\ m4 <= v x /\
    felem_fits5 a m))
  (ensures  (let r = fnegate5 a x in let xn = v x in
    as_nat5 r = 2 * v x * S.prime - as_nat5 a /\
    felem_fits5 r (2*xn,2*xn,2*xn,2*xn,2*xn)))

let fnegate5_lemma m a x =
  let xn = v x in
  let (a0,a1,a2,a3,a4) = a in
  let (m0,m1,m2,m3,m4) = m in
  let r0 = u64 0xffffefffffc2f *. u64 2 *. x -. a0 in
  assert_norm (0xffffefffffc2f < max52);
  assert_norm (max52 < 0xffffefffffc2f * 2);
  lemma_mul_sub m0 (u64 0xffffefffffc2f) x a0;

  let r1 = u64 0xfffffffffffff *. u64 2 *. x -. a1 in
  assert_norm (0xfffffffffffff <= max52);
  assert_norm (max52 <= 0xfffffffffffff * 2);
  lemma_mul_sub m1 (u64 0xfffffffffffff) x a1;

  let r2 = u64 0xfffffffffffff *. u64 2 *. x -. a2 in
  lemma_mul_sub m2 (u64 0xfffffffffffff) x a2;

  let r3 = u64 0xfffffffffffff *. u64 2 *. x -. a3 in
  lemma_mul_sub m3 (u64 0xfffffffffffff) x a3;

  let r4 = u64 0xffffffffffff *. u64 2 *. x -. a4 in
  assert_norm (0xffffffffffff <= max48);
  assert_norm (max48 <= 0xffffffffffff * 2);
  lemma_mul_sub_last m4 (u64 0xffffffffffff) x a4;

  let r = (r0,r1,r2,r3,r4) in
  assert (felem_fits5 r (2*xn,2*xn,2*xn,2*xn,2*xn));
  assert (as_nat5 r =
    0xffffefffffc2f * 2 * v x - v a0 +
    (0xfffffffffffff * 2 * v x - v a1) * pow52 +
    (0xfffffffffffff * 2 * v x - v a2) * pow104 +
    (0xfffffffffffff * 2 * v x - v a3) * pow156 +
    (0xffffffffffff * 2 * v x - v a4) * pow208);

  calc (==) {
    0xffffefffffc2f * 2 * v x - v a0 +
    (0xfffffffffffff * 2 * v x - v a1) * pow52 +
    (0xfffffffffffff * 2 * v x - v a2) * pow104 +
    (0xfffffffffffff * 2 * v x - v a3) * pow156 +
    (0xffffffffffff * 2 * v x - v a4) * pow208;
  (==) {
    Math.Lemmas.paren_mul_right 0xffffefffffc2f 2 (v x);
    Math.Lemmas.paren_mul_right 0xfffffffffffff 2 (v x);
    Math.Lemmas.distributivity_sub_left (2 * v x * 0xfffffffffffff) (v a1) pow52 }
    2 * v x * 0xffffefffffc2f - v a0 +
    2 * v x * 0xfffffffffffff * pow52 - v a1 * pow52 +
    (0xfffffffffffff * 2 * v x - v a2) * pow104 +
    (0xfffffffffffff * 2 * v x - v a3) * pow156 +
    (0xffffffffffff * 2 * v x - v a4) * pow208;
  (==) {
    Math.Lemmas.paren_mul_right 0xfffffffffffff 2 (v x);
    Math.Lemmas.distributivity_sub_left (2 * v x * 0xfffffffffffff) (v a2) pow104;
    Math.Lemmas.distributivity_sub_left (2 * v x * 0xfffffffffffff) (v a3) pow156 }
    2 * v x * 0xffffefffffc2f - v a0 +
    2 * v x * 0xfffffffffffff * pow52 - v a1 * pow52 +
    2 * v x * 0xfffffffffffff * pow104 - v a2 * pow104 +
    2 * v x * 0xfffffffffffff * pow156 - v a3 * pow156 +
    (0xffffffffffff * 2 * v x - v a4) * pow208;
  (==) {
    Math.Lemmas.paren_mul_right 0xffffffffffff 2 (v x);
    Math.Lemmas.distributivity_sub_left (2 * v x * 0xffffffffffff) (v a4) pow208 }
    2 * v x * 0xffffefffffc2f - v a0 +
    2 * v x * 0xfffffffffffff * pow52 - v a1 * pow52 +
    2 * v x * 0xfffffffffffff * pow104 - v a2 * pow104 +
    2 * v x * 0xfffffffffffff * pow156 - v a3 * pow156 +
    2 * v x * 0xffffffffffff * pow208 - v a4 * pow208;
  (==) { L4.lemma_distr5_pow52 (2 * v x) 0xffffefffffc2f 0xfffffffffffff 0xfffffffffffff 0xfffffffffffff 0xffffffffffff }
    - as_nat5 a +
    2 * v x * (0xffffefffffc2f + 0xfffffffffffff * pow52 +
    0xfffffffffffff * pow104 + 0xfffffffffffff * pow156 +  0xffffffffffff * pow208);
  (==) { assert_norm (0xffffefffffc2f + 0xfffffffffffff * pow52 +
    0xfffffffffffff * pow104 + 0xfffffffffffff * pow156 +  0xffffffffffff * pow208 = S.prime) }
    - as_nat5 a + 2 * v x * S.prime;
  };

  assert (as_nat5 r = 2 * v x * S.prime - as_nat5 a)


let sub5_lemma ma mb a b x =
  let (ma0,ma1,ma2,ma3,ma4) = ma in
  let xn = v x in
  let r = fnegate5 b x in
  fnegate5_lemma mb b x;
  let o = add5 a r in
  add5_lemma ma (2*xn,2*xn,2*xn,2*xn,2*xn) a r


let fsub5_lemma ma mb a b x =
  let r = fsub5 a b x in let xn = v x in
  sub5_lemma ma mb a b x;
  assert (as_nat5 r % S.prime = (as_nat5 a - as_nat5 b + 2 * xn * S.prime) % S.prime);
  Math.Lemmas.lemma_mod_plus (as_nat5 a - as_nat5 b) (2 * xn) S.prime;
  assert (as_nat5 r % S.prime = (as_nat5 a - as_nat5 b) % S.prime);
  Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 a) (- as_nat5 b) S.prime;
  Math.Lemmas.lemma_mod_sub_distr (feval5 a) (as_nat5 b) S.prime
