module Hacl.Spec.P256.Qinv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: mv to specs/
let qelem = x:nat{x < S.prime_p256_order}
let qmul (x y:qelem) : qelem = (x * y) % S.prime_p256_order

let nat_mod_comm_monoid = M.mk_nat_mod_comm_monoid S.prime_p256_order

let mk_to_nat_mod_comm_monoid : SE.to_comm_monoid qelem = {
  SE.a_spec = qelem;
  SE.comm_monoid = nat_mod_comm_monoid;
  SE.refl = (fun (x:qelem) -> x);
}

val one_mod : SE.one_st qelem mk_to_nat_mod_comm_monoid
let one_mod _ = 1

val mul_mod : SE.mul_st qelem mk_to_nat_mod_comm_monoid
let mul_mod x y = qmul x y

val sqr_mod : SE.sqr_st qelem mk_to_nat_mod_comm_monoid
let sqr_mod x = qmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops qelem = {
  SE.to = mk_to_nat_mod_comm_monoid;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let qsquare_times (a:qelem) (b:nat) : qelem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val qsquare_times_lemma: a:qelem -> b:nat ->
  Lemma (qsquare_times a b == M.pow a (pow2 b) % S.prime_p256_order)
let qsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_comm_monoid a b;
  assert (qsquare_times a b == LE.pow nat_mod_comm_monoid a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.prime_p256_order a (pow2 b)


let qinv_x8_x128 (x6 x_11: qelem) : qelem =
  let x8 = qmul (qsquare_times x6 2) x_11 in
  let x16 = qmul (qsquare_times x8 8) x8 in
  let x32 = qmul (qsquare_times x16 16) x16 in
  let x96 = qmul (qsquare_times x32 64) x32 in
  let x128 = qmul (qsquare_times x96 32) x32 in
  x128


let qinv_x134_x153 (x128 x_11 x_111 x_1111 x_10101 x_101111: qelem) : qelem =
  let x134 = qmul (qsquare_times x128 6) x_101111 in
  let x139 = qmul (qsquare_times x134 5) x_111 in
  let x143 = qmul (qsquare_times x139 4) x_11 in
  let x148 = qmul (qsquare_times x143 5) x_1111 in
  let x153 = qmul (qsquare_times x148 5) x_10101 in
  x153


let qinv_x153_x177 (x153 x_101 x_111 x_101111: qelem) : qelem =
  let x157 = qmul (qsquare_times x153 4) x_101 in
  let x160 = qmul (qsquare_times x157 3) x_101 in
  let x163 = qmul (qsquare_times x160 3) x_101 in
  let x168 = qmul (qsquare_times x163 5) x_111 in
  let x177 = qmul (qsquare_times x168 9) x_101111 in
  x177


let qinv_x177_x210 (f x177 x_111 x_1111: qelem) : qelem =
  let x183 = qmul (qsquare_times x177 6) x_1111 in
  let x185 = qmul (qsquare_times x183 2) f in
  let x190 = qmul (qsquare_times x185 5) f in
  let x196 = qmul (qsquare_times x190 6) x_1111 in
  let x201 = qmul (qsquare_times x196 5) x_111 in
  let x205 = qmul (qsquare_times x201 4) x_111 in
  let x210 = qmul (qsquare_times x205 5) x_111 in
  x210


let qinv_x210_x240 (x210 x_11 x_101 x_101111: qelem) : qelem =
  let x215 = qmul (qsquare_times x210 5) x_101 in
  let x218 = qmul (qsquare_times x215 3) x_11 in
  let x228 = qmul (qsquare_times x218 10) x_101111 in
  let x230 = qmul (qsquare_times x228 2) x_11 in
  let x235 = qmul (qsquare_times x230 5) x_11 in
  let x240 = qmul (qsquare_times x235 5) x_11 in
  x240


let qinv_x240_x256 (f x240 x_1111 x_10101: qelem) : qelem =
  let x243 = qmul (qsquare_times x240 3) f in
  let x250 = qmul (qsquare_times x243 7) x_10101 in
  let x256 = qmul (qsquare_times x250 6) x_1111 in
  x256


let qinv_x8_x256 (f x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 : qelem) : qelem =
  let x128 = qinv_x8_x128 x6 x_11 in
  let x153 = qinv_x134_x153 x128 x_11 x_111 x_1111 x_10101 x_101111 in
  let x177 = qinv_x153_x177 x153 x_101 x_111 x_101111 in
  let x210 = qinv_x177_x210 f x177 x_111 x_1111 in
  let x240 = qinv_x210_x240 x210 x_11 x_101 x_101111 in
  let x256 = qinv_x240_x256 f x240 x_1111 x_10101 in
  x256


(**
The algorithm is taken from
https://briansmith.org/ecc-inversion-addition-chains-01
*)
val qinv: f:qelem -> qelem
let qinv f =
  let x_10 = qsquare_times f 1 in // x_10 is used 3x
  let x_11 = qmul x_10 f in
  let x_101 = qmul x_10 x_11 in
  let x_111 = qmul x_10 x_101 in

  let x_1010 = qsquare_times x_101 1 in // x_1010 is used 2x
  let x_1111 = qmul x_101 x_1010 in
  let x_10101 = qmul (qsquare_times x_1010 1) f in

  let x_101010 = qsquare_times x_10101 1 in // x_101010 is used 2x
  let x_101111 = qmul x_101 x_101010 in
  let x6 = qmul x_10101 x_101010 in
  qinv_x8_x256 f x6 x_11 x_101 x_111 x_1111 x_10101 x_101111


// TODO: mv to lib/
val lemma_pow_mod_1: f:qelem -> Lemma (f == M.pow f 1 % S.prime_p256_order)
let lemma_pow_mod_1 f =
  M.lemma_pow1 f;
  Math.Lemmas.small_mod f S.prime_p256_order;
  assert_norm (pow2 0 = 1);
  assert (f == M.pow f 1 % S.prime_p256_order)


val lemma_pow_mod_mul: f:qelem -> a:nat -> b:nat ->
  Lemma (qmul (M.pow f a % S.prime_p256_order) (M.pow f b % S.prime_p256_order) == M.pow f (a + b) % S.prime_p256_order)
let lemma_pow_mod_mul f a b =
  calc (==) {
    qmul (M.pow f a % S.prime_p256_order) (M.pow f b % S.prime_p256_order);
    (==) {
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow f a) (M.pow f b % S.prime_p256_order) S.prime_p256_order;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow f a) (M.pow f b) S.prime_p256_order }
    M.pow f a * M.pow f b % S.prime_p256_order;
    (==) { M.lemma_pow_add f a b }
    M.pow f (a + b) % S.prime_p256_order;
  }


val lemma_pow_pow_mod: f:qelem -> a:nat -> b:nat ->
  Lemma (M.pow (M.pow f a % S.prime_p256_order) b % S.prime_p256_order == M.pow f (a * b) % S.prime_p256_order)
let lemma_pow_pow_mod f a b =
  calc (==) {
    M.pow (M.pow f a % S.prime_p256_order) b % S.prime_p256_order;
    (==) { M.lemma_pow_mod_base (M.pow f a) b S.prime_p256_order }
    M.pow (M.pow f a) b % S.prime_p256_order;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) % S.prime_p256_order;
    }


val lemma_pow_pow_mod_mul: f:qelem -> a:nat -> b:nat -> c:nat ->
  Lemma (qmul (M.pow (M.pow f a % S.prime_p256_order) b % S.prime_p256_order) (M.pow f c % S.prime_p256_order) == M.pow f (a * b + c) % S.prime_p256_order)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    qmul (M.pow (M.pow f a % S.prime_p256_order) b % S.prime_p256_order) (M.pow f c % S.prime_p256_order);
    (==) { lemma_pow_pow_mod f a b }
    qmul (M.pow f (a * b) % S.prime_p256_order) (M.pow f c % S.prime_p256_order);
    (==) { lemma_pow_mod_mul f (a * b) c }
    M.pow f (a * b + c) % S.prime_p256_order;
  }

//////////////////////////////

// S.prime_p256_order - 2 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f
val qinv_lemma: f:qelem -> Lemma (qinv f == M.pow f (S.prime_p256_order - 2) % S.prime_p256_order)
let qinv_lemma f =
  let x_10 = qsquare_times f 1 in
  qsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  assert (x_10 == M.pow f 0x2 % S.prime_p256_order);

  let x_11 = qmul x_10 f in
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x_11 == M.pow f 0x3 % S.prime_p256_order);

  let x_101 = qmul x_10 x_11 in
  lemma_pow_mod_mul f 0x2 0x3;
  assert (x_101 == M.pow f 0x5 % S.prime_p256_order);

  let x_111 = qmul x_10 x_101 in
  lemma_pow_mod_mul f 0x2 0x5;
  assert (x_111 == M.pow f 0x7 % S.prime_p256_order);

  let x_1010 = qsquare_times x_101 1 in
  qsquare_times_lemma x_101 1;
  assert_norm (pow2 1 = 2);
  lemma_pow_pow_mod f 0x5 0x2;
  assert (x_1010 == M.pow f 0xa % S.prime_p256_order);

  let x_1111 = qmul x_101 x_1010 in
  lemma_pow_mod_mul f 0x5 0xa;
  assert (x_1111 == M.pow f 0xf % S.prime_p256_order);

  let x_10101 = qmul (qsquare_times x_1010 1) f in
  qsquare_times_lemma x_1010 1;
  lemma_pow_pow_mod_mul f 0xa 0x2 0x1;
  assert (x_10101 == M.pow f 0x15 % S.prime_p256_order);

  let x_101010 = qsquare_times x_10101 1 in
  qsquare_times_lemma x_10101 1;
  lemma_pow_pow_mod f 0x15 0x2;
  assert (x_101010 == M.pow f 0x2a % S.prime_p256_order);

  let x_101111 = qmul x_101 x_101010 in
  lemma_pow_mod_mul f 0x5 0x2a;
  assert (x_101111 == M.pow f 0x2f % S.prime_p256_order);

  let x6 = qmul x_10101 x_101010 in
  lemma_pow_mod_mul f 0x15 0x2a;
  assert (x6 == M.pow f 0x3f % S.prime_p256_order);

  let x8 = qmul (qsquare_times x6 2) x_11 in
  qsquare_times_lemma x6 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0x3f 0x4 0x3;
  assert (x8 == M.pow f 0xff % S.prime_p256_order);

  let x16 = qmul (qsquare_times x8 8) x8 in
  qsquare_times_lemma x8 8;
  assert_norm (pow2 8 = 0x100);
  lemma_pow_pow_mod_mul f 0xff 0x100 0xff;
  assert (x16 == M.pow f 0xffff % S.prime_p256_order);

  let x32 = qmul (qsquare_times x16 16) x16 in
  qsquare_times_lemma x16 16;
  assert_norm (pow2 16 = 0x10000);
  lemma_pow_pow_mod_mul f 0xffff 0x10000 0xffff;
  assert (x32 == M.pow f 0xffffffff % S.prime_p256_order);

  let x96 = qmul (qsquare_times x32 64) x32 in
  qsquare_times_lemma x32 64;
  assert_norm (pow2 64 = 0x10000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x10000000000000000 0xffffffff;
  assert (x96 == M.pow f 0xffffffff00000000ffffffff % S.prime_p256_order);

  let x128 = qmul (qsquare_times x96 32) x32 in
  qsquare_times_lemma x96 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffff 0x100000000 0xffffffff;
  assert (x128 == M.pow f 0xffffffff00000000ffffffffffffffff % S.prime_p256_order);

  let x134 = qmul (qsquare_times x128 6) x_101111 in
  qsquare_times_lemma x128 6;
  assert_norm (pow2 6 = 0x40);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffff 0x40 0x2f;
  assert (x134 == M.pow f 0x3fffffffc00000003fffffffffffffffef % S.prime_p256_order);

  let x139 = qmul (qsquare_times x134 5) x_111 in
  qsquare_times_lemma x134 5;
  assert_norm (pow2 5 = 0x20);
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef 0x20 0x7;
  assert (x139 == M.pow f 0x7fffffff800000007fffffffffffffffde7 % S.prime_p256_order);

  let x143 = qmul (qsquare_times x139 4) x_11 in
  qsquare_times_lemma x139 4;
  assert_norm (pow2 4 = 0x10);
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde7 0x10 0x3;
  assert (x143 == M.pow f 0x7fffffff800000007fffffffffffffffde73 % S.prime_p256_order);

  let x148 = qmul (qsquare_times x143 5) x_1111 in
  qsquare_times_lemma x143 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde73 0x20 0xf;
  assert (x148 == M.pow f 0xffffffff00000000ffffffffffffffffbce6f % S.prime_p256_order);

  let x153 = qmul (qsquare_times x148 5) x_10101 in
  qsquare_times_lemma x148 5;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6f 0x20 0x15;
  assert (x153 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf5 % S.prime_p256_order);

  let x157 = qmul (qsquare_times x153 4) x_101 in
  qsquare_times_lemma x153 4;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf5 0x10 0x5;
  assert (x157 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55 % S.prime_p256_order);

  let x160 = qmul (qsquare_times x157 3) x_101 in
  qsquare_times_lemma x157 3;
  assert_norm (pow2 3 = 0x8);
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55 0x8 0x5;
  assert (x160 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faad % S.prime_p256_order);

  let x163 = qmul (qsquare_times x160 3) x_101 in
  qsquare_times_lemma x160 3;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faad 0x8 0x5;
  assert (x163 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d % S.prime_p256_order);

  let x168 = qmul (qsquare_times x163 5) x_111 in
  qsquare_times_lemma x163 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d 0x20 0x7;
  assert (x168 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7 % S.prime_p256_order);

  let x177 = qmul (qsquare_times x168 9) x_101111 in
  qsquare_times_lemma x168 9;
  assert_norm (pow2 9 = 0x200);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7 0x200 0x2f;
  assert (x177 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f % S.prime_p256_order);

  let x183 = qmul (qsquare_times x177 6) x_1111 in
  qsquare_times_lemma x177 6;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f 0x40 0xf;
  assert (x183 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf % S.prime_p256_order);

  let x185 = qmul (qsquare_times x183 2) f in
  qsquare_times_lemma x183 2;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf 0x4 0x1;
  assert (x185 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d % S.prime_p256_order);

  let x190 = qmul (qsquare_times x185 5) f in
  qsquare_times_lemma x185 5;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d 0x20 0x1;
  assert (x190 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a1 % S.prime_p256_order);

  let x196 = qmul (qsquare_times x190 6) x_1111 in
  qsquare_times_lemma x190 6;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a1 0x40 0xf;
  assert (x196 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f % S.prime_p256_order);

  let x201 = qmul (qsquare_times x196 5) x_111 in
  qsquare_times_lemma x196 5;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f 0x20 0x7;
  assert (x201 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e7 % S.prime_p256_order);

  let x205 = qmul (qsquare_times x201 4) x_111 in
  qsquare_times_lemma x201 4;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e7 0x10 0x7;
  assert (x205 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e77 % S.prime_p256_order);

  let x210 = qmul (qsquare_times x205 5) x_111 in
  qsquare_times_lemma x205 5;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e77 0x20 0x7;
  assert (x210 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee7 % S.prime_p256_order);

  let x215 = qmul (qsquare_times x210 5) x_101 in
  qsquare_times_lemma x210 5;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee7 0x20 0x5;
  assert (x215 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5 % S.prime_p256_order);

  let x218 = qmul (qsquare_times x215 3) x_11 in
  qsquare_times_lemma x215 3;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5 0x8 0x3;
  assert (x218 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b % S.prime_p256_order);

  let x228 = qmul (qsquare_times x218 10) x_101111 in
  qsquare_times_lemma x218 10;
  assert_norm (pow2 10 = 0x400);
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b 0x400 0x2f;
  assert (x228 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f % S.prime_p256_order);

  let x230 = qmul (qsquare_times x228 2) x_11 in
  qsquare_times_lemma x228 2;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f 0x4 0x3;
  assert (x230 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf % S.prime_p256_order);

  let x235 = qmul (qsquare_times x230 5) x_11 in
  qsquare_times_lemma x230 5;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf 0x20 0x3;
  assert (x235 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3 % S.prime_p256_order);

  let x240 = qmul (qsquare_times x235 5) x_11 in
  qsquare_times_lemma x235 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3 0x20 0x3;
  assert (x240 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63 % S.prime_p256_order);

  let x243 = qmul (qsquare_times x240 3) f in
  qsquare_times_lemma x240 3;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63 0x8 0x1;
  assert (x243 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e319 % S.prime_p256_order);

  let x250 = qmul (qsquare_times x243 7) x_10101 in
  qsquare_times_lemma x243 7;
  assert_norm (pow2 7 = 0x80);
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e319 0x80 0x15;
  assert (x250 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf18c95 % S.prime_p256_order);

  let x256 = qmul (qsquare_times x250 6) x_1111 in
  qsquare_times_lemma x250 6;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf18c95 0x40 0xf;
  assert (x256 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f % S.prime_p256_order);

  assert_norm (S.prime_p256_order - 2 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f)
