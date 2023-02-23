module Hacl.Spec.P256.Finv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: mv to specs/
let felem = x:nat{x < S.prime256}
let fmul (x y:felem) : felem = (x * y) % S.prime256

let nat_mod_comm_monoid = M.mk_nat_mod_comm_monoid S.prime256

let mk_to_nat_mod_comm_monoid : SE.to_comm_monoid felem = {
  SE.a_spec = felem;
  SE.comm_monoid = nat_mod_comm_monoid;
  SE.refl = (fun (x:felem) -> x);
}

val one_mod : SE.one_st felem mk_to_nat_mod_comm_monoid
let one_mod _ = 1

val mul_mod : SE.mul_st felem mk_to_nat_mod_comm_monoid
let mul_mod x y = fmul x y

val sqr_mod : SE.sqr_st felem mk_to_nat_mod_comm_monoid
let sqr_mod x = fmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops felem = {
  SE.to = mk_to_nat_mod_comm_monoid;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let fsquare_times (a:felem) (b:nat) : felem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val fsquare_times_lemma: a:felem -> b:nat ->
  Lemma (fsquare_times a b == M.pow a (pow2 b) % S.prime256)
let fsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_comm_monoid a b;
  assert (fsquare_times a b == LE.pow nat_mod_comm_monoid a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.prime256 a (pow2 b)


(**
The algorithm is taken from
https://briansmith.org/ecc-inversion-addition-chains-01
*)
val finv: f:felem -> felem
let finv f =
  let x2 = fmul (fsquare_times f 1) f in
  let x3 = fmul (fsquare_times x2 1) f in
  let x6 = fmul (fsquare_times x3 3) x3 in
  let x12 = fmul (fsquare_times x6 6) x6 in
  let x15 = fmul (fsquare_times x12 3) x3 in
  let x30 = fmul (fsquare_times x15 15) x15 in
  let x32 = fmul (fsquare_times x30 2) x2 in
  let x64 = fmul (fsquare_times x32 32) f in
  let x192 = fmul (fsquare_times x64 128) x32 in
  let x224 = fmul (fsquare_times x192 32) x32 in
  let x254 = fmul (fsquare_times x224 30) x30 in
  let x256 = fmul (fsquare_times x254 2) f in
  x256


val fsqrt: f:felem -> felem
let fsqrt f =
  let x2 = fmul (fsquare_times f 1) f in
  let x4 = fmul (fsquare_times x2 2) x2 in
  let x8 = fmul (fsquare_times x4 4) x4 in
  let x16 = fmul (fsquare_times x8 8) x8 in
  let x32 = fmul (fsquare_times x16 16) x16 in
  let x64 = fmul (fsquare_times x32 32) f in
  let x160 = fmul (fsquare_times x64 96) f in
  let x254 = fsquare_times x160 94 in
  x254


// TODO: mv to lib/
val lemma_pow_mod_1: f:felem -> Lemma (f == M.pow f 1 % S.prime256)
let lemma_pow_mod_1 f =
  M.lemma_pow1 f;
  Math.Lemmas.small_mod f S.prime256;
  assert_norm (pow2 0 = 1);
  assert (f == M.pow f 1 % S.prime256)


val lemma_pow_mod_mul: f:felem -> a:nat -> b:nat ->
  Lemma (fmul (M.pow f a % S.prime256) (M.pow f b % S.prime256) == M.pow f (a + b) % S.prime256)
let lemma_pow_mod_mul f a b =
  calc (==) {
    fmul (M.pow f a % S.prime256) (M.pow f b % S.prime256);
    (==) {
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow f a) (M.pow f b % S.prime256) S.prime256;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow f a) (M.pow f b) S.prime256 }
    M.pow f a * M.pow f b % S.prime256;
    (==) { M.lemma_pow_add f a b }
    M.pow f (a + b) % S.prime256;
  }


val lemma_pow_pow_mod: f:felem -> a:nat -> b:nat ->
  Lemma (M.pow (M.pow f a % S.prime256) b % S.prime256 == M.pow f (a * b) % S.prime256)
let lemma_pow_pow_mod f a b =
  calc (==) {
    M.pow (M.pow f a % S.prime256) b % S.prime256;
    (==) { M.lemma_pow_mod_base (M.pow f a) b S.prime256 }
    M.pow (M.pow f a) b % S.prime256;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) % S.prime256;
    }


val lemma_pow_pow_mod_mul: f:felem -> a:nat -> b:nat -> c:nat ->
  Lemma (fmul (M.pow (M.pow f a % S.prime256) b % S.prime256) (M.pow f c % S.prime256) == M.pow f (a * b + c) % S.prime256)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    fmul (M.pow (M.pow f a % S.prime256) b % S.prime256) (M.pow f c % S.prime256);
    (==) { lemma_pow_pow_mod f a b }
    fmul (M.pow f (a * b) % S.prime256) (M.pow f c % S.prime256);
    (==) { lemma_pow_mod_mul f (a * b) c }
    M.pow f (a * b + c) % S.prime256;
  }

//////////////////////////////

// prime256 - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd
val finv_lemma: f:felem -> Lemma (finv f == M.pow f (S.prime256 - 2) % S.prime256)
let finv_lemma f =
  let x2 = fmul (fsquare_times f 1) f in
  fsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x2 == M.pow f 0x3 % S.prime256);

  let x3 = fmul (fsquare_times x2 1) f in
  fsquare_times_lemma x2 1;
  lemma_pow_mod_1 f;
  lemma_pow_pow_mod_mul f 0x3 0x2 0x1;
  assert (x3 == M.pow f 0x7 % S.prime256);

  let x6 = fmul (fsquare_times x3 3) x3 in
  fsquare_times_lemma x3 3;
  assert_norm (pow2 3 = 8);
  lemma_pow_pow_mod_mul f 0x7 0x8 0x7;
  assert (x6 == M.pow f 0x3f % S.prime256);

  let x12 = fmul (fsquare_times x6 6) x6 in
  fsquare_times_lemma x6 6;
  assert_norm (pow2 6 = 64);
  lemma_pow_pow_mod_mul f 0x3f 0x40 0x3f;
  assert (x12 == M.pow f 0xfff % S.prime256);

  let x15 = fmul (fsquare_times x12 3) x3 in
  fsquare_times_lemma x12 3;
  lemma_pow_pow_mod_mul f 0xfff 0x8 0x7;
  assert (x15 == M.pow f 0x7fff % S.prime256);

  let x30 = fmul (fsquare_times x15 15) x15 in
  fsquare_times_lemma x15 15;
  assert_norm (pow2 15 = 0x8000);
  lemma_pow_pow_mod_mul f 0x7fff 0x8000 0x7fff;
  assert (x30 == M.pow f 0x3fffffff % S.prime256);

  let x32 = fmul (fsquare_times x30 2) x2 in
  fsquare_times_lemma x30 2;
  assert_norm (pow2 2 = 4);
  lemma_pow_pow_mod_mul f 0x3fffffff 0x4 0x3;
  assert (x32 == M.pow f 0xffffffff % S.prime256);

  let x64 = fmul (fsquare_times x32 32) f in
  fsquare_times_lemma x32 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x100000000 0x1;
  assert (x64 == M.pow f 0xffffffff00000001 % S.prime256);

  let x192 = fmul (fsquare_times x64 128) x32 in
  fsquare_times_lemma x64 128;
  assert_norm (pow2 128 = 0x100000000000000000000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001 0x100000000000000000000000000000000 0xffffffff;
  assert (x192 == M.pow f 0xffffffff00000001000000000000000000000000ffffffff % S.prime256);

  let x224 = fmul (fsquare_times x192 32) x32 in
  fsquare_times_lemma x192 32;
  lemma_pow_pow_mod_mul f 0xffffffff00000001000000000000000000000000ffffffff 0x100000000 0xffffffff;
  assert (x224 == M.pow f 0xffffffff00000001000000000000000000000000ffffffffffffffff % S.prime256);

  let x254 = fmul (fsquare_times x224 30) x30 in
  fsquare_times_lemma x224 30;
  assert_norm (pow2 30 = 0x40000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001000000000000000000000000ffffffffffffffff 0x40000000 0x3fffffff;
  assert (x254 == M.pow f 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff % S.prime256);

  let x256 = fmul (fsquare_times x254 2) f in
  fsquare_times_lemma x254 2;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff 0x4 0x1;
  assert (x256 == M.pow f 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd % S.prime256);

  assert_norm (S.prime256 - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd)


// (prime256 + 1) / 4 = 0x3fffffffc0000000400000000000000000000000400000000000000000000000
val fsqrt_lemma: f:felem -> Lemma (fsqrt f == M.pow f ((S.prime256 + 1) / 4) % S.prime256)
let fsqrt_lemma f =
  let x2 = fmul (fsquare_times f 1) f in
  fsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x2 == M.pow f 0x3 % S.prime256);

  let x4 = fmul (fsquare_times x2 2) x2 in
  fsquare_times_lemma x2 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0x3 0x4 0x3;
  assert (x4 == M.pow f 0xf % S.prime256);

  let x8 = fmul (fsquare_times x4 4) x4 in
  fsquare_times_lemma x4 4;
  assert_norm (pow2 4 = 0x10);
  lemma_pow_pow_mod_mul f 0xf 0x10 0xf;
  assert (x8 == M.pow f 0xff % S.prime256);

  let x16 = fmul (fsquare_times x8 8) x8 in
  fsquare_times_lemma x8 8;
  assert_norm (pow2 8 = 0x100);
  lemma_pow_pow_mod_mul f 0xff 0x100 0xff;
  assert (x16 == M.pow f 0xffff % S.prime256);

  let x32 = fmul (fsquare_times x16 16) x16 in
  fsquare_times_lemma x16 16;
  assert_norm (pow2 16 = 0x10000);
  lemma_pow_pow_mod_mul f 0xffff 0x10000 0xffff;
  assert (x32 == M.pow f 0xffffffff % S.prime256);

  let x64 = fmul (fsquare_times x32 32) f in
  fsquare_times_lemma x32 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x100000000 0x1;
  assert (x64 == M.pow f 0xffffffff00000001 % S.prime256);

  let x160 = fmul (fsquare_times x64 96) f in
  fsquare_times_lemma x64 96;
  assert_norm (pow2 96 = 0x1000000000000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001 0x1000000000000000000000000 0x1;
  assert (x160 == M.pow f 0xffffffff00000001000000000000000000000001 % S.prime256);

  let x254 = fsquare_times x160 94 in
  fsquare_times_lemma x160 94;
  assert_norm (pow2 94 = 0x400000000000000000000000);
  lemma_pow_pow_mod f 0xffffffff00000001000000000000000000000001 0x400000000000000000000000;
  assert (x254 == M.pow f 0x3fffffffc0000000400000000000000000000000400000000000000000000000 % S.prime256);

  assert_norm ((S.prime256 + 1) / 4 = 0x3fffffffc0000000400000000000000000000000400000000000000000000000)
