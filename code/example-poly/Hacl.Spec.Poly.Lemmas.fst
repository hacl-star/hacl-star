module Hacl.Spec.Poly.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Poly

module S = Spec.Poly
module L = Hacl.Spec.Poly.Lemmas0

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val add5_lemma: f1:felem5 -> f2:felem5 -> Lemma
  (requires
    felem_fits5 f1 (2,2,2,2,2) /\
    felem_fits5 f2 (1,1,1,1,1))
  (ensures (let res = add5 f1 f2 in
    felem_fits5 res (3,3,3,3,3) /\
    feval5 res == S.fadd (feval5 f1) (feval5 f2)))
  [SMTPat (add5 f1 f2)]

let add5_lemma f1 f2 =
  let res = add5 f1 f2 in
  let (f10, f11, f12, f13, f14) = f1 in
  let (f20, f21, f22, f23, f24) = f2 in
  Math.Lemmas.modulo_lemma (v f10 + v f20) (pow2 64);
  Math.Lemmas.modulo_lemma (v f11 + v f21) (pow2 64);
  Math.Lemmas.modulo_lemma (v f12 + v f20) (pow2 64);
  Math.Lemmas.modulo_lemma (v f13 + v f23) (pow2 64);
  Math.Lemmas.modulo_lemma (v f14 + v f24) (pow2 64);
  assert (felem_fits5 res (3,3,3,3,3));
  assert (as_nat5 res == as_nat5 f1 + as_nat5 f2);
  Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 f1) (as_nat5 f2) S.prime;
  Math.Lemmas.lemma_mod_plus_distr_r (as_nat5 f1 % S.prime) (as_nat5 f2) S.prime


val smul_mod_lemma: #m1:scale32 -> #m2:scale32 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a m1 /\ felem_fits1 b m2)
  (ensures (let res = a *. b in
    v res == v a * v b /\ felem_wide_fits1 res (m1 * m2)))

let smul_mod_lemma #m1 #m2 a b =
  L.lemma_mult_le (v a) (m1 * max26) (v b) (m2 * max26);
  assert (v a * v b <= m1 * m2 * max26 * max26);
  Math.Lemmas.modulo_lemma (v a * v b) (pow2 64)


val smul5_lemma: #m1:scale32 -> #m2:scale32_5 -> u1:uint64 -> f2:felem5 -> Lemma
  (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
  (ensures (let res = smul5 u1 f2 in
    felem_wide_fits5 res (m1 *^ m2) /\
    as_nat5 res == v u1 * as_nat5 f2))

let smul5_lemma #m1 #m2 u1 f2 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let res = smul5 u1 f2 in
  smul_mod_lemma #m1 #m20 u1 f20;
  smul_mod_lemma #m1 #m21 u1 f21;
  smul_mod_lemma #m1 #m22 u1 f22;
  smul_mod_lemma #m1 #m23 u1 f23;
  smul_mod_lemma #m1 #m24 u1 f24;
  assert (felem_wide_fits5 res (m1 *^ m2));

  calc (==) {
    v u1 * as_nat5 f2;
    (==) { L.lemma_mul5_distr_l_pow (v u1) (v f20) (v f21) (v f22) (v f23) (v f24) }
    v u1 * v f20 + v u1 * v f21 * pow26 + v u1 * v f22 * pow52 + v u1 * v f23 * pow78 + v u1 * v f24 * pow104;
    (==) {  }
    as_nat5 res;
    }


val smul_add_mod_lemma: #m1:scale32 -> #m2:scale32 -> #m3:scale64
  -> a:uint64 -> b:uint64 -> c:uint64 -> Lemma
  (requires
    felem_fits1 a m1 /\ felem_fits1 b m2 /\
    felem_wide_fits1 c m3 /\ m3 + m1 * m2 <= 4096)
  (ensures (let res = c +. a *. b in
    v res == v c + v a * v b /\ felem_wide_fits1 res (m3 + m1 * m2)))

let smul_add_mod_lemma #m1 #m2 #m3 a b c =
  assert_norm ((m3 + m1 * m2) * max26 * max26 < pow2 64);
  L.lemma_mult_le (v a) (m1 * max26) (v b) (m2 * max26);
  assert (v c + v a * v b <= m3 * max26 * max26 + m1 * m2 * max26 * max26);
  Math.Lemmas.modulo_lemma (v c + v a * v b) (pow2 64)


val smul_add5_lemma: #m1:scale32 -> #m2:scale32_5 -> #m3:scale64_5 ->
  u1:uint64 -> f2:felem5 -> acc1:felem_wide5 -> Lemma
  (requires
    felem_fits1 u1 m1 /\ felem_fits5 f2 m2 /\
    felem_wide_fits5 acc1 m3 /\
    m3 +* m1 *^ m2 <=* s64x5 4096)
  (ensures (let res = smul_add5 u1 f2 acc1 in
    felem_wide_fits5 res (m3 +* m1 *^ m2) /\
    as_nat5 res == as_nat5 acc1 + v u1 * as_nat5 f2))

let smul_add5_lemma #m1 #m2 #m3 u1 f2 acc1 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (a0, a1, a2, a3, a4) = acc1 in
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  let res = smul_add5 u1 f2 acc1 in
  smul_add_mod_lemma #m1 #m20 #m30 u1 f20 a0;
  smul_add_mod_lemma #m1 #m21 #m31 u1 f21 a1;
  smul_add_mod_lemma #m1 #m22 #m32 u1 f22 a2;
  smul_add_mod_lemma #m1 #m23 #m33 u1 f23 a3;
  smul_add_mod_lemma #m1 #m24 #m34 u1 f24 a4;
  assert (felem_wide_fits5 res (m3 +* m1 *^ m2));

  calc (==) {
    v u1 * as_nat5 f2;
    (==) { L.lemma_mul5_distr_l_pow (v u1) (v f20) (v f21) (v f22) (v f23) (v f24) }
    v u1 * v f20 + v u1 * v f21 * pow26 + v u1 * v f22 * pow52 + v u1 * v f23 * pow78 + v u1 * v f24 * pow104;
    }


val mul5_lemma: f1:felem5 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 f1 (3, 3, 3, 3, 3) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r5 (5, 5, 5, 5, 5) /\
    r5 == precomp_r5 r)
  (ensures (let res = mul5 f1 r r5 in
    felem_wide_fits5 res (63, 51, 39, 27, 15) /\
    feval5 res == S.fmul (feval5 f1) (feval5 r)))
  [SMTPat (mul5 f1 r r5)]

let mul5_lemma f1 r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in
  let res = mul5 f1 r r5 in

  let (a0,a1,a2,a3,a4) = smul5 f10 (r0,r1,r2,r3,r4) in
  smul5_lemma #3 #(1,1,1,1,1) f10 (r0,r1,r2,r3,r4);
  let (a10,a11,a12,a13,a14) = smul_add5 f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add5_lemma #3 #(5,1,1,1,1) #(3,3,3,3,3) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  let (a20,a21,a22,a23,a24) = smul_add5 f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add5_lemma #3 #(5,5,1,1,1) #(18,6,6,6,6) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  let (a30,a31,a32,a33,a34) = smul_add5 f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add5_lemma #3 #(5,5,5,1,1) #(33,21,9,9,9) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  let (a40,a41,a42,a43,a44) = smul_add5 f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add5_lemma #3 #(5,5,5,5,1) #(48,36,24,12,12) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34);
  assert (felem_wide_fits5 (mul5 f1 r r5) (63, 51, 39, 27, 15));

  assert (as_nat5 res ==
    v f10 * as_nat5 (r0,r1,r2,r3,r4) +
    v f11 * as_nat5 (r54,r0,r1,r2,r3) +
    v f12 * as_nat5 (r53,r54,r0,r1,r2) +
    v f13 * as_nat5 (r52,r53,r54,r0,r1) +
    v f14 * as_nat5 (r51,r52,r53,r54,r0));
  L.mul5_nat_lemma f1 r r5


val carry26_lemma: #m0:scale32 -> #m1:scale64 -> l:uint64 -> cin:uint64 -> Lemma
  (requires felem_fits1 l m0 /\ v cin <= m1 * max26)
  (ensures  (let l0, l1 = carry26 l cin in
    felem_fits1 l0 1 /\ v l1 <= m0 + m1 /\
    v l + v cin == v l1 * pow26 + v l0))

let carry26_lemma #m l cin =
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  Math.Lemmas.euclidean_division_definition (v l') (pow2 26)


val carry26_wide_lemma: #m:scale64 -> l:uint64 -> cin:uint64 -> Lemma
  (requires felem_wide_fits1 l m /\ v cin <= 4096 * max26)
  (ensures  (let l0, l1 = carry26_wide l cin in
    felem_fits1 l0 1 /\ v l1 <= (m + 1) * max26 /\
    v l + v cin == v l1 * pow26 + v l0))

let carry26_wide_lemma #m l cin =
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  Math.Lemmas.euclidean_division_definition (v l') (pow2 26)


val carry_wide_felem5_lemma: f:felem_wide5 -> Lemma
  (requires felem_wide_fits5 f (63, 51, 39, 27, 15))
  (ensures (let res = carry_wide_felem5 f in
    felem_fits5 res (1, 2, 1, 1, 1) /\
    feval5 res == feval5 f))

let carry_wide_felem5_lemma f =
  let res = carry_wide_felem5 f in
  let (i0, i1, i2, i3, i4) = f in
  let t0,c0 = carry26_wide i0 (u64 0) in
  carry26_wide_lemma #63 i0 (u64 0);
  let t1,c1 = carry26_wide i1 c0 in
  carry26_wide_lemma #51 i1 c0;
  let t2,c2 = carry26_wide i2 c1 in
  carry26_wide_lemma #39 i2 c1;
  let t3,c3 = carry26_wide i3 c2 in
  carry26_wide_lemma #27 i3 c2;
  let t4,c4 = carry26_wide i4 c3 in
  carry26_wide_lemma #15 i4 c3;
  assert (felem_fits5 (t0, t1, t2, t3, t4) (1, 1, 1, 1, 1));
  assert (v c4 <= 16 * max26);

  Math.Lemmas.small_mod (v c4 * 5) (pow2 64);
  assert (v (c4 *. u64 5) == v (c4 *! u64 5));
  carry26_lemma #1 #80 t0 (c4 *! u64 5);
  let t0,c5 = carry26 t0 (c4 *! u64 5) in

  Math.Lemmas.small_mod (v t1 + v c5) (pow2 64);
  assert (v (t1 +! c5) == v (t1 +. c5));
  let t1 = t1 +! c5 in
  assert (felem_fits5 res (1, 2, 1, 1, 1));

  assert (as_nat5 res ==
    (v i0 - v c0 * pow26 + v c4 * 5 - v c5 * pow26) +
    (v i1 + v c0 - v c1 * pow26 + v c5) * pow26 +
    (v i2 + v c1 - v c2 * pow26) * pow52 +
    (v i3 + v c2 - v c3 * pow26) * pow78 +
    (v i4 + v c3 - v c4 * pow26) * pow104);
  L.carry_wide_felem5_nat_lemma f c0 c1 c2 c3 c4 c5


val add_mul_r5_lemma: acc:felem5 -> f1:felem5 -> r:felem5 -> r5:felem5 -> Lemma
  (requires
    felem_fits5 acc (2, 2, 2, 2, 2) /\
    felem_fits5 f1 (1, 1, 1, 1, 1) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r5 (5, 5, 5, 5, 5) /\
    r5 == precomp_r5 r)
  (ensures (let res = add_mul_r5 acc f1 r r5 in
    feval5 res == S.fmul (S.fadd (feval5 acc) (feval5 f1)) (feval5 r) /\
    felem_fits5 res (2, 2, 2, 2, 2)))
  [SMTPat (add_mul_r5 acc f1 r r5)]

let add_mul_r5_lemma acc f1 r r5 =
  let acc1 = add5 acc f1 in
  let tmp = mul5 acc1 r r5 in
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_lemma tmp;
  assert (feval5 res == S.fmul (S.fadd (feval5 acc) (feval5 f1)) (feval5 r));
  assert (felem_fits5 res (2, 2, 2, 2, 2))
