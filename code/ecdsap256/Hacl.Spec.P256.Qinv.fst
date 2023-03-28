module Hacl.Spec.P256.Qinv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nat_mod_comm_monoid = M.mk_nat_mod_comm_monoid S.order

let mk_to_nat_mod_comm_monoid : SE.to_comm_monoid S.qelem = {
  SE.a_spec = S.qelem;
  SE.comm_monoid = nat_mod_comm_monoid;
  SE.refl = (fun (x:S.qelem) -> x);
}

val one_mod : SE.one_st S.qelem mk_to_nat_mod_comm_monoid
let one_mod _ = 1

val mul_mod : SE.mul_st S.qelem mk_to_nat_mod_comm_monoid
let mul_mod x y = S.qmul x y

val sqr_mod : SE.sqr_st S.qelem mk_to_nat_mod_comm_monoid
let sqr_mod x = S.qmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops S.qelem = {
  SE.to = mk_to_nat_mod_comm_monoid;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let qsquare_times (a:S.qelem) (b:nat) : S.qelem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val qsquare_times_lemma: a:S.qelem -> b:nat ->
  Lemma (qsquare_times a b == M.pow a (pow2 b) % S.order)
let qsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_comm_monoid a b;
  assert (qsquare_times a b == LE.pow nat_mod_comm_monoid a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.order a (pow2 b)


let qinv_x8_x128 (x6 x_11: S.qelem) : S.qelem =
  let x8 = S.qmul (qsquare_times x6 2) x_11 in
  let x16 = S.qmul (qsquare_times x8 8) x8 in
  let x32 = S.qmul (qsquare_times x16 16) x16 in
  let x96 = S.qmul (qsquare_times x32 64) x32 in
  let x128 = S.qmul (qsquare_times x96 32) x32 in
  x128


let qinv_x134_x153 (x128 x_11 x_111 x_1111 x_10101 x_101111: S.qelem) : S.qelem =
  let x134 = S.qmul (qsquare_times x128 6) x_101111 in
  let x139 = S.qmul (qsquare_times x134 5) x_111 in
  let x143 = S.qmul (qsquare_times x139 4) x_11 in
  let x148 = S.qmul (qsquare_times x143 5) x_1111 in
  let x153 = S.qmul (qsquare_times x148 5) x_10101 in
  x153


let qinv_x153_x177 (x153 x_101 x_111 x_101111: S.qelem) : S.qelem =
  let x157 = S.qmul (qsquare_times x153 4) x_101 in
  let x160 = S.qmul (qsquare_times x157 3) x_101 in
  let x163 = S.qmul (qsquare_times x160 3) x_101 in
  let x168 = S.qmul (qsquare_times x163 5) x_111 in
  let x177 = S.qmul (qsquare_times x168 9) x_101111 in
  x177


let qinv_x177_x210 (f x177 x_111 x_1111: S.qelem) : S.qelem =
  let x183 = S.qmul (qsquare_times x177 6) x_1111 in
  let x185 = S.qmul (qsquare_times x183 2) f in
  let x190 = S.qmul (qsquare_times x185 5) f in
  let x196 = S.qmul (qsquare_times x190 6) x_1111 in
  let x201 = S.qmul (qsquare_times x196 5) x_111 in
  let x205 = S.qmul (qsquare_times x201 4) x_111 in
  let x210 = S.qmul (qsquare_times x205 5) x_111 in
  x210


let qinv_x210_x240 (x210 x_11 x_101 x_101111: S.qelem) : S.qelem =
  let x215 = S.qmul (qsquare_times x210 5) x_101 in
  let x218 = S.qmul (qsquare_times x215 3) x_11 in
  let x228 = S.qmul (qsquare_times x218 10) x_101111 in
  let x230 = S.qmul (qsquare_times x228 2) x_11 in
  let x235 = S.qmul (qsquare_times x230 5) x_11 in
  let x240 = S.qmul (qsquare_times x235 5) x_11 in
  x240


let qinv_x240_x256 (f x240 x_1111 x_10101: S.qelem) : S.qelem =
  let x243 = S.qmul (qsquare_times x240 3) f in
  let x250 = S.qmul (qsquare_times x243 7) x_10101 in
  let x256 = S.qmul (qsquare_times x250 6) x_1111 in
  x256


let qinv_x8_x256 (f x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 : S.qelem) : S.qelem =
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
val qinv: f:S.qelem -> S.qelem
let qinv f =
  let x_10 = qsquare_times f 1 in // x_10 is used 3x
  let x_11 = S.qmul x_10 f in
  let x_101 = S.qmul x_10 x_11 in
  let x_111 = S.qmul x_10 x_101 in

  let x_1010 = qsquare_times x_101 1 in // x_1010 is used 2x
  let x_1111 = S.qmul x_101 x_1010 in
  let x_10101 = S.qmul (qsquare_times x_1010 1) f in

  let x_101010 = qsquare_times x_10101 1 in // x_101010 is used 2x
  let x_101111 = S.qmul x_101 x_101010 in
  let x6 = S.qmul x_10101 x_101010 in
  qinv_x8_x256 f x6 x_11 x_101 x_111 x_1111 x_10101 x_101111


// TODO: mv to lib/
val lemma_pow_mod_1: f:S.qelem -> Lemma (f == M.pow f 1 % S.order)
let lemma_pow_mod_1 f =
  M.lemma_pow1 f;
  Math.Lemmas.small_mod f S.order;
  assert_norm (pow2 0 = 1);
  assert (f == M.pow f 1 % S.order)


val lemma_pow_mod_mul: f:S.qelem -> a:nat -> b:nat ->
  Lemma (S.qmul (M.pow f a % S.order) (M.pow f b % S.order) == M.pow f (a + b) % S.order)
let lemma_pow_mod_mul f a b =
  calc (==) {
    S.qmul (M.pow f a % S.order) (M.pow f b % S.order);
    (==) {
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow f a) (M.pow f b % S.order) S.order;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow f a) (M.pow f b) S.order }
    M.pow f a * M.pow f b % S.order;
    (==) { M.lemma_pow_add f a b }
    M.pow f (a + b) % S.order;
  }


val lemma_pow_pow_mod: f:S.qelem -> a:nat -> b:nat ->
  Lemma (M.pow (M.pow f a % S.order) b % S.order == M.pow f (a * b) % S.order)
let lemma_pow_pow_mod f a b =
  calc (==) {
    M.pow (M.pow f a % S.order) b % S.order;
    (==) { M.lemma_pow_mod_base (M.pow f a) b S.order }
    M.pow (M.pow f a) b % S.order;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) % S.order;
    }


val lemma_pow_pow_mod_mul: f:S.qelem -> a:nat -> b:nat -> c:nat ->
  Lemma (S.qmul (M.pow (M.pow f a % S.order) b % S.order) (M.pow f c % S.order) == M.pow f (a * b + c) % S.order)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    S.qmul (M.pow (M.pow f a % S.order) b % S.order) (M.pow f c % S.order);
    (==) { lemma_pow_pow_mod f a b }
    S.qmul (M.pow f (a * b) % S.order) (M.pow f c % S.order);
    (==) { lemma_pow_mod_mul f (a * b) c }
    M.pow f (a * b + c) % S.order;
  }

//////////////////////////////

// S.order - 2 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f
val qinv_lemma: f:S.qelem -> Lemma (qinv f == M.pow f (S.order - 2) % S.order)
let qinv_lemma f =
  let x_10 = qsquare_times f 1 in
  qsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  assert (x_10 == M.pow f 0x2 % S.order);

  let x_11 = S.qmul x_10 f in
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x_11 == M.pow f 0x3 % S.order);

  let x_101 = S.qmul x_10 x_11 in
  lemma_pow_mod_mul f 0x2 0x3;
  assert (x_101 == M.pow f 0x5 % S.order);

  let x_111 = S.qmul x_10 x_101 in
  lemma_pow_mod_mul f 0x2 0x5;
  assert (x_111 == M.pow f 0x7 % S.order);

  let x_1010 = qsquare_times x_101 1 in
  qsquare_times_lemma x_101 1;
  assert_norm (pow2 1 = 2);
  lemma_pow_pow_mod f 0x5 0x2;
  assert (x_1010 == M.pow f 0xa % S.order);

  let x_1111 = S.qmul x_101 x_1010 in
  lemma_pow_mod_mul f 0x5 0xa;
  assert (x_1111 == M.pow f 0xf % S.order);

  let x_10101 = S.qmul (qsquare_times x_1010 1) f in
  qsquare_times_lemma x_1010 1;
  lemma_pow_pow_mod_mul f 0xa 0x2 0x1;
  assert (x_10101 == M.pow f 0x15 % S.order);

  let x_101010 = qsquare_times x_10101 1 in
  qsquare_times_lemma x_10101 1;
  lemma_pow_pow_mod f 0x15 0x2;
  assert (x_101010 == M.pow f 0x2a % S.order);

  let x_101111 = S.qmul x_101 x_101010 in
  lemma_pow_mod_mul f 0x5 0x2a;
  assert (x_101111 == M.pow f 0x2f % S.order);

  let x6 = S.qmul x_10101 x_101010 in
  lemma_pow_mod_mul f 0x15 0x2a;
  assert (x6 == M.pow f 0x3f % S.order);

  let x8 = S.qmul (qsquare_times x6 2) x_11 in
  qsquare_times_lemma x6 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0x3f 0x4 0x3;
  assert (x8 == M.pow f 0xff % S.order);

  let x16 = S.qmul (qsquare_times x8 8) x8 in
  qsquare_times_lemma x8 8;
  assert_norm (pow2 8 = 0x100);
  lemma_pow_pow_mod_mul f 0xff 0x100 0xff;
  assert (x16 == M.pow f 0xffff % S.order);

  let x32 = S.qmul (qsquare_times x16 16) x16 in
  qsquare_times_lemma x16 16;
  assert_norm (pow2 16 = 0x10000);
  lemma_pow_pow_mod_mul f 0xffff 0x10000 0xffff;
  assert (x32 == M.pow f 0xffffffff % S.order);

  let x96 = S.qmul (qsquare_times x32 64) x32 in
  qsquare_times_lemma x32 64;
  assert_norm (pow2 64 = 0x10000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x10000000000000000 0xffffffff;
  assert (x96 == M.pow f 0xffffffff00000000ffffffff % S.order);

  let x128 = S.qmul (qsquare_times x96 32) x32 in
  qsquare_times_lemma x96 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffff 0x100000000 0xffffffff;
  assert (x128 == M.pow f 0xffffffff00000000ffffffffffffffff % S.order);

  let x134 = S.qmul (qsquare_times x128 6) x_101111 in
  qsquare_times_lemma x128 6;
  assert_norm (pow2 6 = 0x40);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffff 0x40 0x2f;
  assert (x134 == M.pow f 0x3fffffffc00000003fffffffffffffffef % S.order);

  let x139 = S.qmul (qsquare_times x134 5) x_111 in
  qsquare_times_lemma x134 5;
  assert_norm (pow2 5 = 0x20);
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef 0x20 0x7;
  assert (x139 == M.pow f 0x7fffffff800000007fffffffffffffffde7 % S.order);

  let x143 = S.qmul (qsquare_times x139 4) x_11 in
  qsquare_times_lemma x139 4;
  assert_norm (pow2 4 = 0x10);
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde7 0x10 0x3;
  assert (x143 == M.pow f 0x7fffffff800000007fffffffffffffffde73 % S.order);

  let x148 = S.qmul (qsquare_times x143 5) x_1111 in
  qsquare_times_lemma x143 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde73 0x20 0xf;
  assert (x148 == M.pow f 0xffffffff00000000ffffffffffffffffbce6f % S.order);

  let x153 = S.qmul (qsquare_times x148 5) x_10101 in
  qsquare_times_lemma x148 5;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6f 0x20 0x15;
  assert (x153 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf5 % S.order);

  let x157 = S.qmul (qsquare_times x153 4) x_101 in
  qsquare_times_lemma x153 4;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf5 0x10 0x5;
  assert (x157 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55 % S.order);

  let x160 = S.qmul (qsquare_times x157 3) x_101 in
  qsquare_times_lemma x157 3;
  assert_norm (pow2 3 = 0x8);
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55 0x8 0x5;
  assert (x160 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faad % S.order);

  let x163 = S.qmul (qsquare_times x160 3) x_101 in
  qsquare_times_lemma x160 3;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faad 0x8 0x5;
  assert (x163 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d % S.order);

  let x168 = S.qmul (qsquare_times x163 5) x_111 in
  qsquare_times_lemma x163 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d 0x20 0x7;
  assert (x168 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7 % S.order);

  let x177 = S.qmul (qsquare_times x168 9) x_101111 in
  qsquare_times_lemma x168 9;
  assert_norm (pow2 9 = 0x200);
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7 0x200 0x2f;
  assert (x177 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f % S.order);

  let x183 = S.qmul (qsquare_times x177 6) x_1111 in
  qsquare_times_lemma x177 6;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f 0x40 0xf;
  assert (x183 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf % S.order);

  let x185 = S.qmul (qsquare_times x183 2) f in
  qsquare_times_lemma x183 2;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf 0x4 0x1;
  assert (x185 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d % S.order);

  let x190 = S.qmul (qsquare_times x185 5) f in
  qsquare_times_lemma x185 5;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d 0x20 0x1;
  assert (x190 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a1 % S.order);

  let x196 = S.qmul (qsquare_times x190 6) x_1111 in
  qsquare_times_lemma x190 6;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a1 0x40 0xf;
  assert (x196 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f % S.order);

  let x201 = S.qmul (qsquare_times x196 5) x_111 in
  qsquare_times_lemma x196 5;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f 0x20 0x7;
  assert (x201 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e7 % S.order);

  let x205 = S.qmul (qsquare_times x201 4) x_111 in
  qsquare_times_lemma x201 4;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e7 0x10 0x7;
  assert (x205 == M.pow f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e77 % S.order);

  let x210 = S.qmul (qsquare_times x205 5) x_111 in
  qsquare_times_lemma x205 5;
  lemma_pow_pow_mod_mul f 0x1fffffffe00000001ffffffffffffffff79cdf55b4e2f3d09e77 0x20 0x7;
  assert (x210 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee7 % S.order);

  let x215 = S.qmul (qsquare_times x210 5) x_101 in
  qsquare_times_lemma x210 5;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee7 0x20 0x5;
  assert (x215 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5 % S.order);

  let x218 = S.qmul (qsquare_times x215 3) x_11 in
  qsquare_times_lemma x215 3;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5 0x8 0x3;
  assert (x218 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b % S.order);

  let x228 = S.qmul (qsquare_times x218 10) x_101111 in
  qsquare_times_lemma x218 10;
  assert_norm (pow2 10 = 0x400);
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b 0x400 0x2f;
  assert (x228 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f % S.order);

  let x230 = S.qmul (qsquare_times x228 2) x_11 in
  qsquare_times_lemma x228 2;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f 0x4 0x3;
  assert (x230 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf % S.order);

  let x235 = S.qmul (qsquare_times x230 5) x_11 in
  qsquare_times_lemma x230 5;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf 0x20 0x3;
  assert (x235 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3 % S.order);

  let x240 = S.qmul (qsquare_times x235 5) x_11 in
  qsquare_times_lemma x235 5;
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3 0x20 0x3;
  assert (x240 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63 % S.order);

  let x243 = S.qmul (qsquare_times x240 3) f in
  qsquare_times_lemma x240 3;
  lemma_pow_pow_mod_mul f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63 0x8 0x1;
  assert (x243 == M.pow f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e319 % S.order);

  let x250 = S.qmul (qsquare_times x243 7) x_10101 in
  qsquare_times_lemma x243 7;
  assert_norm (pow2 7 = 0x80);
  lemma_pow_pow_mod_mul f 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e319 0x80 0x15;
  assert (x250 == M.pow f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf18c95 % S.order);

  let x256 = S.qmul (qsquare_times x250 6) x_1111 in
  qsquare_times_lemma x250 6;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000003fffffffffffffffef39beab69c5e7a13cee72b0bf18c95 0x40 0xf;
  assert (x256 == M.pow f 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f % S.order);

  assert_norm (S.order - 2 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f)


val qinv_is_qinv_lemma: f:S.qelem -> Lemma (qinv f == S.qinv f)
let qinv_is_qinv_lemma f =
  qinv_lemma f;
  assert (qinv f == M.pow f (S.order - 2) % S.order);
  M.lemma_pow_mod #S.order f (S.order - 2)
