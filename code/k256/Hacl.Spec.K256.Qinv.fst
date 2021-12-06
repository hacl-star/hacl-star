module Hacl.Spec.K256.Qinv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nat_mod_cm = M.mk_nat_mod_comm_monoid S.q

let mk_to_nat_mod_cm : SE.to_cm S.qelem = {
  SE.a_spec = S.qelem;
  SE.cm = nat_mod_cm;
  SE.refl = (fun (x:S.qelem) -> x);
}

val one_mod : SE.one_st S.qelem mk_to_nat_mod_cm
let one_mod _ = 1

val mul_mod : SE.mul_st S.qelem mk_to_nat_mod_cm
let mul_mod x y = S.qmul x y

val sqr_mod : SE.sqr_st S.qelem mk_to_nat_mod_cm
let sqr_mod x = S.qmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops S.qelem = {
  SE.to = mk_to_nat_mod_cm;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let qsquare_times (a:S.qelem) (b:nat) : S.qelem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val qsquare_times_lemma: a:S.qelem -> b:nat ->
  Lemma (qsquare_times a b == M.pow a (pow2 b) % S.q)
let qsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_cm a b;
  assert (qsquare_times a b == LE.pow nat_mod_cm a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.q a (pow2 b)


(**
The algorithm is taken from
https://briansmith.org/ecc-inversion-addition-chains-01
*)

val qinv_r0_r1 (x14: S.qelem) : S.qelem
let qinv_r0_r1 x14 =
  let x28 = S.qmul (qsquare_times x14 14) x14 in
  let x56 = S.qmul (qsquare_times x28 28) x28 in
  let r0 = S.qmul (qsquare_times x56 56) x56 in
  let r1 = S.qmul (qsquare_times r0 14) x14 in
  r1


val qinv_r2_r8 (r1 x_101 x_111 x_1011: S.qelem) : S.qelem
let qinv_r2_r8 r1 x_101 x_111 x_1011 =
  let r2 = S.qmul (qsquare_times r1 3) x_101 in
  let r3 = S.qmul (qsquare_times r2 4) x_111 in
  let r4 = S.qmul (qsquare_times r3 4) x_101 in
  let r5 = S.qmul (qsquare_times r4 5) x_1011 in
  let r6 = S.qmul (qsquare_times r5 4) x_1011 in
  let r7 = S.qmul (qsquare_times r6 4) x_111 in
  let r8 = S.qmul (qsquare_times r7 5) x_111 in
  r8


val qinv_r9_r15 (r8 x_101 x_111 x_1001 x_1101: S.qelem) : S.qelem
let qinv_r9_r15 r8 x_101 x_111 x_1001 x_1101 =
  let r9 = S.qmul (qsquare_times r8 6) x_1101 in
  let r10 = S.qmul (qsquare_times r9 4) x_101 in
  let r11 = S.qmul (qsquare_times r10 3) x_111 in
  let r12 = S.qmul (qsquare_times r11 5) x_1001 in
  let r13 = S.qmul (qsquare_times r12 6) x_101 in
  let r14 = S.qmul (qsquare_times r13 10) x_111 in
  let r15 = S.qmul (qsquare_times r14 4) x_111 in
  r15


val qinv_r16_r23 (r15 x8 x_11 x_1001 x_1011 x_1101: S.qelem) : S.qelem
let qinv_r16_r23 r15 x8 x_11 x_1001 x_1011 x_1101 =
  let r16 = S.qmul (qsquare_times r15 9) x8 in
  let r17 = S.qmul (qsquare_times r16 5) x_1001 in
  let r18 = S.qmul (qsquare_times r17 6) x_1011 in
  let r19 = S.qmul (qsquare_times r18 4) x_1101 in
  let r20 = S.qmul (qsquare_times r19 5) x_11 in
  let r21 = S.qmul (qsquare_times r20 6) x_1101 in
  let r22 = S.qmul (qsquare_times r21 10) x_1101 in
  let r23 = S.qmul (qsquare_times r22 4) x_1001 in
  r23


val qinv_r24_r25 (r23 x_1 x6: S.qelem) : S.qelem
let qinv_r24_r25 r23 x_1 x6 =
  let r24 = S.qmul (qsquare_times r23 6) x_1 in
  let r25 = S.qmul (qsquare_times r24 8) x6 in
  r25


val qinv_r0_r25 (x_1 x_11 x_101 x_111 x_1001 x_1011 x_1101: S.qelem) : S.qelem
let qinv_r0_r25 x_1 x_11 x_101 x_111 x_1001 x_1011 x_1101 =
  let x6 = S.qmul (qsquare_times x_1101 2) x_1011 in
  let x8 = S.qmul (qsquare_times x6 2) x_11 in
  let x14 = S.qmul (qsquare_times x8 6) x6 in

  let r1 = qinv_r0_r1 x14 in
  let r8 = qinv_r2_r8 r1 x_101 x_111 x_1011 in
  let r15 = qinv_r9_r15 r8 x_101 x_111 x_1001 x_1101 in
  let r23 = qinv_r16_r23 r15 x8 x_11 x_1001 x_1011 x_1101 in
  qinv_r24_r25 r23 x_1 x6


val qinv: f:S.qelem -> S.qelem
let qinv f =
  let x_1 = f in
  let x_10 = qsquare_times f 1 in
  let x_11 = S.qmul x_10 x_1 in
  let x_101 = S.qmul x_10 x_11 in
  let x_111 = S.qmul x_10 x_101 in
  let x_1001 = S.qmul x_10 x_111 in
  let x_1011 = S.qmul x_10 x_1001 in
  let x_1101 = S.qmul x_10 x_1011 in

  qinv_r0_r25 x_1 x_11 x_101 x_111 x_1001 x_1011 x_1101


val lemma_pow_mod_1: f:S.qelem -> Lemma (f == M.pow f 1 % S.q)
let lemma_pow_mod_1 f =
  M.lemma_pow1 f;
  Math.Lemmas.small_mod f S.q;
  assert_norm (pow2 0 = 1);
  assert (f == M.pow f 1 % S.q)


val lemma_pow_mod_mul: f:S.qelem -> a:nat -> b:nat ->
  Lemma (S.qmul (M.pow f a % S.q) (M.pow f b % S.q) == M.pow f (a + b) % S.q)
let lemma_pow_mod_mul f a b =
  calc (==) {
    S.qmul (M.pow f a % S.q) (M.pow f b % S.q);
    (==) {
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow f a) (M.pow f b % S.q) S.q;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow f a) (M.pow f b) S.q }
    M.pow f a * M.pow f b % S.q;
    (==) { M.lemma_pow_add f a b }
    M.pow f (a + b) % S.q;
  }


val lemma_pow_pow_mod_mul: f:S.qelem -> a:nat -> b:nat -> c:nat ->
  Lemma (S.qmul (M.pow (M.pow f a % S.q) b % S.q) (M.pow f c % S.q) == M.pow f (a * b + c) % S.q)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    S.qmul (M.pow (M.pow f a % S.q) b % S.q) (M.pow f c % S.q);
    (==) {
      M.lemma_pow_mod_base (M.pow f a) b S.q;
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow (M.pow f a) b) (M.pow f c % S.q) S.q;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow (M.pow f a) b) (M.pow f c) S.q }
    M.pow (M.pow f a) b * M.pow f c % S.q;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) * M.pow f c % S.q;
    (==) { M.lemma_pow_add f (a * b) c }
    M.pow f (a * b + c) % S.q;
  }


// S.q - 2 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd036413f
val qinv_lemma: f:S.qelem -> Lemma (qinv f == M.pow f (S.q - 2) % S.q)
let qinv_lemma f =
  let x_1 = f in

  let x_10 = qsquare_times f 1 in
  qsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  assert (x_10 == M.pow f 0x2 % S.q);

  let x_11 = S.qmul x_10 x_1 in
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x_11 == M.pow f 0x3 % S.q);

  let x_101 = S.qmul x_10 x_11 in
  lemma_pow_mod_mul f 0x2 0x3;
  assert (x_101 == M.pow f 0x5 % S.q);

  let x_111 = S.qmul x_10 x_101 in
  lemma_pow_mod_mul f 0x2 0x5;
  assert (x_111 == M.pow f 0x7 % S.q);

  let x_1001 = S.qmul x_10 x_111 in
  lemma_pow_mod_mul f 0x2 0x7;
  assert (x_1001 == M.pow f 0x9 % S.q);

  let x_1011 = S.qmul x_10 x_1001 in
  lemma_pow_mod_mul f 0x2 0x9;
  assert (x_1011 == M.pow f 0xb % S.q);

  let x_1101 = S.qmul x_10 x_1011 in
  lemma_pow_mod_mul f 0x2 0xb;
  assert (x_1101 == M.pow f 0xd % S.q);

  let x6 = S.qmul (qsquare_times x_1101 2) x_1011 in
  qsquare_times_lemma x_1101 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0xd 0x4 0xb;
  assert (x6 == M.pow f 0x3f % S.q);

  let x8 = S.qmul (qsquare_times x6 2) x_11 in
  qsquare_times_lemma x6 2;
  lemma_pow_pow_mod_mul f 0x3f 0x4 0x3;
  assert (x8 == M.pow f 0xff % S.q);

  let x14 = S.qmul (qsquare_times x8 6) x6 in
  qsquare_times_lemma x8 6;
  assert_norm (pow2 6 = 0x40);
  lemma_pow_pow_mod_mul f 0xff 0x40 0x3f;
  assert (x14 == M.pow f 0x3fff % S.q);

  let x28 = S.qmul (qsquare_times x14 14) x14 in
  qsquare_times_lemma x14 14;
  assert_norm (pow2 14 = 0x4000);
  lemma_pow_pow_mod_mul f 0x3fff 0x4000 0x3fff;
  assert (x28 == M.pow f 0xfffffff % S.q);

  let x56 = S.qmul (qsquare_times x28 28) x28 in
  qsquare_times_lemma x28 28;
  assert_norm (pow2 28 = 0x10000000);
  lemma_pow_pow_mod_mul f 0xfffffff 0x10000000 0xfffffff;
  assert (x56 == M.pow f 0xffffffffffffff % S.q);

  let r0 = S.qmul (qsquare_times x56 56) x56 in
  qsquare_times_lemma x56 56;
  assert_norm (pow2 56 = 0x100000000000000);
  lemma_pow_pow_mod_mul f 0xffffffffffffff 0x100000000000000 0xffffffffffffff;
  assert (r0 == M.pow f 0xffffffffffffffffffffffffffff % S.q);

  let r1 = S.qmul (qsquare_times r0 14) x14 in
  qsquare_times_lemma r0 14;
  lemma_pow_pow_mod_mul f 0xffffffffffffffffffffffffffff 0x4000 0x3fff;
  assert (r1 == M.pow f 0x3fffffffffffffffffffffffffffffff % S.q);

  let r2 = S.qmul (qsquare_times r1 3) x_101 in
  qsquare_times_lemma r1 3;
  assert_norm (pow2 3 = 0x8);
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffff 0x8 0x5;
  assert (r2 == M.pow f 0x1fffffffffffffffffffffffffffffffd % S.q);

  let r3 = S.qmul (qsquare_times r2 4) x_111 in
  qsquare_times_lemma r2 4;
  assert_norm (pow2 4 = 0x10);
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd 0x10 0x7;
  assert (r3 == M.pow f 0x1fffffffffffffffffffffffffffffffd7 % S.q);

  let r4 = S.qmul (qsquare_times r3 4) x_101 in
  qsquare_times_lemma r3 4;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd7 0x10 0x5;
  assert (r4 == M.pow f 0x1fffffffffffffffffffffffffffffffd75 % S.q);

  let r5 = S.qmul (qsquare_times r4 5) x_1011 in
  qsquare_times_lemma r4 5;
  assert_norm (pow2 5 = 0x20);
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd75 0x20 0xb;
  assert (r5 == M.pow f 0x3fffffffffffffffffffffffffffffffaeab % S.q);

  let r6 = S.qmul (qsquare_times r5 4) x_1011 in
  qsquare_times_lemma r5 4;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeab 0x10 0xb;
  assert (r6 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb % S.q);

  let r7 = S.qmul (qsquare_times r6 4) x_111 in
  qsquare_times_lemma r6 4;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb 0x10 0x7;
  assert (r7 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb7 % S.q);

  let r8 = S.qmul (qsquare_times r7 5) x_111 in
  qsquare_times_lemma r7 5;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb7 0x20 0x7;
  assert (r8 == M.pow f 0x7fffffffffffffffffffffffffffffff5d576e7 % S.q);

  let r9 = S.qmul (qsquare_times r8 6) x_1101 in
  qsquare_times_lemma r8 6;
  lemma_pow_pow_mod_mul f 0x7fffffffffffffffffffffffffffffff5d576e7 0x40 0xd;
  assert (r9 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd % S.q);

  let r10 = S.qmul (qsquare_times r9 4) x_101 in
  qsquare_times_lemma r9 4;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd 0x10 0x5;
  assert (r10 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5 % S.q);

  let r11 = S.qmul (qsquare_times r10 3) x_111 in
  qsquare_times_lemma r10 3;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5 0x8 0x7;
  assert (r11 == M.pow f 0xfffffffffffffffffffffffffffffffebaaedce6af % S.q);

  let r12 = S.qmul (qsquare_times r11 5) x_1001 in
  qsquare_times_lemma r11 5;
  lemma_pow_pow_mod_mul f 0xfffffffffffffffffffffffffffffffebaaedce6af 0x20 0x9;
  assert (r12 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9 % S.q);

  let r13 = S.qmul (qsquare_times r12 6) x_101 in
  qsquare_times_lemma r12 6;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9 0x40 0x5;
  assert (r13 == M.pow f 0x7fffffffffffffffffffffffffffffff5d576e7357a45 % S.q);

  let r14 = S.qmul (qsquare_times r13 10) x_111 in
  qsquare_times_lemma r13 10;
  assert_norm (pow2 10 = 0x400);
  lemma_pow_pow_mod_mul f 0x7fffffffffffffffffffffffffffffff5d576e7357a45 0x400 0x7;
  assert (r14 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5e91407 % S.q);

  let r15 = S.qmul (qsquare_times r14 4) x_111 in
  qsquare_times_lemma r14 4;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5e91407 0x10 0x7;
  assert (r15 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5e914077 % S.q);

  let r16 = S.qmul (qsquare_times r15 9) x8 in
  qsquare_times_lemma r15 9;
  assert_norm (pow2 9 = 0x200);
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5e914077 0x200 0xff;
  assert (r16 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff % S.q);

  let r17 = S.qmul (qsquare_times r16 5) x_1001 in
  qsquare_times_lemma r16 5;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff 0x20 0x9;
  assert (r17 == M.pow f 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe9 % S.q);

  let r18 = S.qmul (qsquare_times r17 6) x_1011 in
  qsquare_times_lemma r17 6;
  lemma_pow_pow_mod_mul f 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe9 0x40 0xb;
  assert (r18 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9140777fa4b % S.q);

  let r19 = S.qmul (qsquare_times r18 4) x_1101 in
  qsquare_times_lemma r18 4;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9140777fa4b 0x10 0xd;
  assert (r19 == M.pow f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9140777fa4bd % S.q);

  let r20 = S.qmul (qsquare_times r19 5) x_11 in
  qsquare_times_lemma r19 5;
  lemma_pow_pow_mod_mul f 0x1fffffffffffffffffffffffffffffffd755db9cd5e9140777fa4bd 0x20 0x3;
  assert (r20 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3 % S.q);

  let r21 = S.qmul (qsquare_times r20 6) x_1101 in
  qsquare_times_lemma r20 6;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3 0x40 0xd;
  assert (r21 == M.pow f 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd % S.q);

  let r22 = S.qmul (qsquare_times r21 10) x_1101 in
  qsquare_times_lemma r21 10;
  lemma_pow_pow_mod_mul f 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd 0x400 0xd;
  assert (r22 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3340d % S.q);

  let r23 = S.qmul (qsquare_times r22 4) x_1001 in
  qsquare_times_lemma r22 4;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3340d 0x10 0x9;
  assert (r23 == M.pow f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3340d9 % S.q);

  let r24 = S.qmul (qsquare_times r23 6) x_1 in
  qsquare_times_lemma r23 6;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffaeabb739abd2280eeff497a3340d9 0x40 0x1;
  assert (r24 == M.pow f 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd03641 % S.q);

  let r25 = S.qmul (qsquare_times r24 8) x6 in
  qsquare_times_lemma r24 8;
  assert_norm (pow2 8 = 0x100);
  lemma_pow_pow_mod_mul f 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd03641 0x100 0x3f;
  assert (r25 == M.pow f 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd036413f % S.q)


val qinv_is_qinv_lemma: f:S.qelem -> Lemma (qinv f == S.qinv f)
let qinv_is_qinv_lemma f =
  qinv_lemma f;
  assert (qinv f == M.pow f (S.q - 2) % S.q);
  M.lemma_pow_mod #S.q f (S.q - 2)
