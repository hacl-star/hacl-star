module Hacl.Spec.P256.Finv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nat_mod_comm_monoid = M.mk_nat_mod_comm_monoid S.prime

let mk_to_nat_mod_comm_monoid : SE.to_comm_monoid S.felem = {
  SE.a_spec = S.felem;
  SE.comm_monoid = nat_mod_comm_monoid;
  SE.refl = (fun (x:S.felem) -> x);
}

val one_mod : SE.one_st S.felem mk_to_nat_mod_comm_monoid
let one_mod _ = 1

val mul_mod : SE.mul_st S.felem mk_to_nat_mod_comm_monoid
let mul_mod x y = S.fmul x y

val sqr_mod : SE.sqr_st S.felem mk_to_nat_mod_comm_monoid
let sqr_mod x = S.fmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops S.felem = {
  SE.to = mk_to_nat_mod_comm_monoid;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let fsquare_times (a:S.felem) (b:nat) : S.felem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val fsquare_times_lemma: a:S.felem -> b:nat ->
  Lemma (fsquare_times a b == M.pow a (pow2 b) % S.prime)
let fsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_comm_monoid a b;
  assert (fsquare_times a b == LE.pow nat_mod_comm_monoid a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.prime a (pow2 b)


(**
The algorithm is taken from
https://briansmith.org/ecc-inversion-addition-chains-01
*)
val finv: f:S.felem -> S.felem
let finv f =
  let x2 = S.fmul (fsquare_times f 1) f in
  let x3 = S.fmul (fsquare_times x2 1) f in
  let x6 = S.fmul (fsquare_times x3 3) x3 in
  let x12 = S.fmul (fsquare_times x6 6) x6 in
  let x15 = S.fmul (fsquare_times x12 3) x3 in
  let x30 = S.fmul (fsquare_times x15 15) x15 in
  let x32 = S.fmul (fsquare_times x30 2) x2 in
  let x64 = S.fmul (fsquare_times x32 32) f in
  let x192 = S.fmul (fsquare_times x64 128) x32 in
  let x224 = S.fmul (fsquare_times x192 32) x32 in
  let x254 = S.fmul (fsquare_times x224 30) x30 in
  let x256 = S.fmul (fsquare_times x254 2) f in
  x256


val fsqrt: f:S.felem -> S.felem
let fsqrt f =
  let x2 = S.fmul (fsquare_times f 1) f in
  let x4 = S.fmul (fsquare_times x2 2) x2 in
  let x8 = S.fmul (fsquare_times x4 4) x4 in
  let x16 = S.fmul (fsquare_times x8 8) x8 in
  let x32 = S.fmul (fsquare_times x16 16) x16 in
  let x64 = S.fmul (fsquare_times x32 32) f in
  let x160 = S.fmul (fsquare_times x64 96) f in
  let x254 = fsquare_times x160 94 in
  x254


// TODO: mv to lib/
val lemma_pow_mod_1: f:S.felem -> Lemma (f == M.pow f 1 % S.prime)
let lemma_pow_mod_1 f =
  M.lemma_pow1 f;
  Math.Lemmas.small_mod f S.prime;
  assert_norm (pow2 0 = 1);
  assert (f == M.pow f 1 % S.prime)


val lemma_pow_mod_mul: f:S.felem -> a:nat -> b:nat ->
  Lemma (S.fmul (M.pow f a % S.prime) (M.pow f b % S.prime) == M.pow f (a + b) % S.prime)
let lemma_pow_mod_mul f a b =
  calc (==) {
    S.fmul (M.pow f a % S.prime) (M.pow f b % S.prime);
    (==) {
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow f a) (M.pow f b % S.prime) S.prime;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow f a) (M.pow f b) S.prime }
    M.pow f a * M.pow f b % S.prime;
    (==) { M.lemma_pow_add f a b }
    M.pow f (a + b) % S.prime;
  }


val lemma_pow_pow_mod: f:S.felem -> a:nat -> b:nat ->
  Lemma (M.pow (M.pow f a % S.prime) b % S.prime == M.pow f (a * b) % S.prime)
let lemma_pow_pow_mod f a b =
  calc (==) {
    M.pow (M.pow f a % S.prime) b % S.prime;
    (==) { M.lemma_pow_mod_base (M.pow f a) b S.prime }
    M.pow (M.pow f a) b % S.prime;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) % S.prime;
    }


val lemma_pow_pow_mod_mul: f:S.felem -> a:nat -> b:nat -> c:nat ->
  Lemma (S.fmul (M.pow (M.pow f a % S.prime) b % S.prime) (M.pow f c % S.prime) == M.pow f (a * b + c) % S.prime)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    S.fmul (M.pow (M.pow f a % S.prime) b % S.prime) (M.pow f c % S.prime);
    (==) { lemma_pow_pow_mod f a b }
    S.fmul (M.pow f (a * b) % S.prime) (M.pow f c % S.prime);
    (==) { lemma_pow_mod_mul f (a * b) c }
    M.pow f (a * b + c) % S.prime;
  }

//////////////////////////////

// prime - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd
val finv_lemma: f:S.felem -> Lemma (finv f == M.pow f (S.prime - 2) % S.prime)
let finv_lemma f =
  let x2 = S.fmul (fsquare_times f 1) f in
  fsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x2 == M.pow f 0x3 % S.prime);

  let x3 = S.fmul (fsquare_times x2 1) f in
  fsquare_times_lemma x2 1;
  lemma_pow_mod_1 f;
  lemma_pow_pow_mod_mul f 0x3 0x2 0x1;
  assert (x3 == M.pow f 0x7 % S.prime);

  let x6 = S.fmul (fsquare_times x3 3) x3 in
  fsquare_times_lemma x3 3;
  assert_norm (pow2 3 = 8);
  lemma_pow_pow_mod_mul f 0x7 0x8 0x7;
  assert (x6 == M.pow f 0x3f % S.prime);

  let x12 = S.fmul (fsquare_times x6 6) x6 in
  fsquare_times_lemma x6 6;
  assert_norm (pow2 6 = 64);
  lemma_pow_pow_mod_mul f 0x3f 0x40 0x3f;
  assert (x12 == M.pow f 0xfff % S.prime);

  let x15 = S.fmul (fsquare_times x12 3) x3 in
  fsquare_times_lemma x12 3;
  lemma_pow_pow_mod_mul f 0xfff 0x8 0x7;
  assert (x15 == M.pow f 0x7fff % S.prime);

  let x30 = S.fmul (fsquare_times x15 15) x15 in
  fsquare_times_lemma x15 15;
  assert_norm (pow2 15 = 0x8000);
  lemma_pow_pow_mod_mul f 0x7fff 0x8000 0x7fff;
  assert (x30 == M.pow f 0x3fffffff % S.prime);

  let x32 = S.fmul (fsquare_times x30 2) x2 in
  fsquare_times_lemma x30 2;
  assert_norm (pow2 2 = 4);
  lemma_pow_pow_mod_mul f 0x3fffffff 0x4 0x3;
  assert (x32 == M.pow f 0xffffffff % S.prime);

  let x64 = S.fmul (fsquare_times x32 32) f in
  fsquare_times_lemma x32 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x100000000 0x1;
  assert (x64 == M.pow f 0xffffffff00000001 % S.prime);

  let x192 = S.fmul (fsquare_times x64 128) x32 in
  fsquare_times_lemma x64 128;
  assert_norm (pow2 128 = 0x100000000000000000000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001 0x100000000000000000000000000000000 0xffffffff;
  assert (x192 == M.pow f 0xffffffff00000001000000000000000000000000ffffffff % S.prime);

  let x224 = S.fmul (fsquare_times x192 32) x32 in
  fsquare_times_lemma x192 32;
  lemma_pow_pow_mod_mul f 0xffffffff00000001000000000000000000000000ffffffff 0x100000000 0xffffffff;
  assert (x224 == M.pow f 0xffffffff00000001000000000000000000000000ffffffffffffffff % S.prime);

  let x254 = S.fmul (fsquare_times x224 30) x30 in
  fsquare_times_lemma x224 30;
  assert_norm (pow2 30 = 0x40000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001000000000000000000000000ffffffffffffffff 0x40000000 0x3fffffff;
  assert (x254 == M.pow f 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff % S.prime);

  let x256 = S.fmul (fsquare_times x254 2) f in
  fsquare_times_lemma x254 2;
  lemma_pow_pow_mod_mul f 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff 0x4 0x1;
  assert (x256 == M.pow f 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd % S.prime);

  assert_norm (S.prime - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd)


val finv_is_finv_lemma: f:S.felem -> Lemma (finv f == S.finv f)
let finv_is_finv_lemma f =
  finv_lemma f;
  assert (finv f == M.pow f (S.prime - 2) % S.prime);
  M.lemma_pow_mod #S.prime f (S.prime - 2)


// (prime + 1) / 4 = 0x3fffffffc0000000400000000000000000000000400000000000000000000000
val fsqrt_lemma: f:S.felem -> Lemma (fsqrt f == M.pow f ((S.prime + 1) / 4) % S.prime)
let fsqrt_lemma f =
  let x2 = S.fmul (fsquare_times f 1) f in
  fsquare_times_lemma f 1;
  assert_norm (pow2 1 = 0x2);
  lemma_pow_mod_1 f;
  lemma_pow_mod_mul f 0x2 0x1;
  assert (x2 == M.pow f 0x3 % S.prime);

  let x4 = S.fmul (fsquare_times x2 2) x2 in
  fsquare_times_lemma x2 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0x3 0x4 0x3;
  assert (x4 == M.pow f 0xf % S.prime);

  let x8 = S.fmul (fsquare_times x4 4) x4 in
  fsquare_times_lemma x4 4;
  assert_norm (pow2 4 = 0x10);
  lemma_pow_pow_mod_mul f 0xf 0x10 0xf;
  assert (x8 == M.pow f 0xff % S.prime);

  let x16 = S.fmul (fsquare_times x8 8) x8 in
  fsquare_times_lemma x8 8;
  assert_norm (pow2 8 = 0x100);
  lemma_pow_pow_mod_mul f 0xff 0x100 0xff;
  assert (x16 == M.pow f 0xffff % S.prime);

  let x32 = S.fmul (fsquare_times x16 16) x16 in
  fsquare_times_lemma x16 16;
  assert_norm (pow2 16 = 0x10000);
  lemma_pow_pow_mod_mul f 0xffff 0x10000 0xffff;
  assert (x32 == M.pow f 0xffffffff % S.prime);

  let x64 = S.fmul (fsquare_times x32 32) f in
  fsquare_times_lemma x32 32;
  assert_norm (pow2 32 = 0x100000000);
  lemma_pow_pow_mod_mul f 0xffffffff 0x100000000 0x1;
  assert (x64 == M.pow f 0xffffffff00000001 % S.prime);

  let x160 = S.fmul (fsquare_times x64 96) f in
  fsquare_times_lemma x64 96;
  assert_norm (pow2 96 = 0x1000000000000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffff00000001 0x1000000000000000000000000 0x1;
  assert (x160 == M.pow f 0xffffffff00000001000000000000000000000001 % S.prime);

  let x254 = fsquare_times x160 94 in
  fsquare_times_lemma x160 94;
  assert_norm (pow2 94 = 0x400000000000000000000000);
  lemma_pow_pow_mod f 0xffffffff00000001000000000000000000000001 0x400000000000000000000000;
  assert (x254 == M.pow f 0x3fffffffc0000000400000000000000000000000400000000000000000000000 % S.prime);

  assert_norm ((S.prime + 1) / 4 = 0x3fffffffc0000000400000000000000000000000400000000000000000000000)


val fsqrt_is_fsqrt_lemma: f:S.felem -> Lemma (fsqrt f == S.fsqrt f)
let fsqrt_is_fsqrt_lemma f =
  fsqrt_lemma f;
  assert (fsqrt f == M.pow f ((S.prime + 1) / 4) % S.prime);
  M.lemma_pow_mod #S.prime f ((S.prime + 1) / 4)
