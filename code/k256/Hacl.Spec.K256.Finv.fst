module Hacl.Spec.K256.Finv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nat_mod_cm = M.mk_nat_mod_comm_monoid S.prime

let mk_to_nat_mod_cm : SE.to_cm S.felem = {
  SE.a_spec = S.felem;
  SE.cm = nat_mod_cm;
  SE.refl = (fun (x:S.felem) -> x);
}

val one_mod : SE.one_st S.felem mk_to_nat_mod_cm
let one_mod _ = S.one

val mul_mod : SE.mul_st S.felem mk_to_nat_mod_cm
let mul_mod x y = S.fmul x y

val sqr_mod : SE.sqr_st S.felem mk_to_nat_mod_cm
let sqr_mod x = S.fmul x x

let mk_nat_mod_concrete_ops : SE.concrete_ops S.felem = {
  SE.to = mk_to_nat_mod_cm;
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
  LE.exp_pow2_lemma nat_mod_cm a b;
  assert (fsquare_times a b == LE.pow nat_mod_cm a (pow2 b));
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
  let x9 = S.fmul (fsquare_times x6 3) x3 in
  let x11 = S.fmul (fsquare_times x9 2) x2 in
  let x22 = S.fmul (fsquare_times x11 11) x11 in
  let x44 = S.fmul (fsquare_times x22 22) x22 in
  let x88 = S.fmul (fsquare_times x44 44) x44 in
  let x176 = S.fmul (fsquare_times x88 88) x88 in
  let x220 = S.fmul (fsquare_times x176 44) x44 in
  let x223 = S.fmul (fsquare_times x220 3) x3 in

  let r = S.fmul (fsquare_times x223 23) x22 in
  let r = S.fmul (fsquare_times r 5) f in
  let r = S.fmul (fsquare_times r 3) x2 in
  let r = S.fmul (fsquare_times r 2) f in
  r


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


val lemma_pow_pow_mod_mul: f:S.felem -> a:nat -> b:nat -> c:nat ->
  Lemma (S.fmul (M.pow (M.pow f a % S.prime) b % S.prime) (M.pow f c % S.prime) == M.pow f (a * b + c) % S.prime)
let lemma_pow_pow_mod_mul f a b c =
  calc (==) {
    S.fmul (M.pow (M.pow f a % S.prime) b % S.prime) (M.pow f c % S.prime);
    (==) {
      M.lemma_pow_mod_base (M.pow f a) b S.prime;
      Math.Lemmas.lemma_mod_mul_distr_l (M.pow (M.pow f a) b) (M.pow f c % S.prime) S.prime;
      Math.Lemmas.lemma_mod_mul_distr_r (M.pow (M.pow f a) b) (M.pow f c) S.prime }
    M.pow (M.pow f a) b * M.pow f c % S.prime;
    (==) { M.lemma_pow_mul f a b }
    M.pow f (a * b) * M.pow f c % S.prime;
    (==) { M.lemma_pow_add f (a * b) c }
    M.pow f (a * b + c) % S.prime;
  }


// S.prime - 2 = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2d
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

  let x9 = S.fmul (fsquare_times x6 3) x3 in
  fsquare_times_lemma x6 3;
  lemma_pow_pow_mod_mul f 0x3f 0x8 0x7;
  assert (x9 == M.pow f 0x1ff % S.prime);

  let x11 = S.fmul (fsquare_times x9 2) x2 in
  fsquare_times_lemma x9 2;
  assert_norm (pow2 2 = 0x4);
  lemma_pow_pow_mod_mul f 0x1ff 0x4 0x3;
  assert (x11 == M.pow f 0x7ff % S.prime);

  let x22 = S.fmul (fsquare_times x11 11) x11 in
  fsquare_times_lemma x11 11;
  assert_norm (pow2 11 = 0x800);
  lemma_pow_pow_mod_mul f 0x7ff 0x800 0x7ff;
  assert (x22 == M.pow f 0x3fffff % S.prime);

  let x44 = S.fmul (fsquare_times x22 22) x22 in
  fsquare_times_lemma x22 22;
  assert_norm (pow2 22 = 0x400000);
  lemma_pow_pow_mod_mul f 0x3fffff 0x400000 0x3fffff;
  assert (x44 == M.pow f 0xfffffffffff % S.prime);

  let x88 = S.fmul (fsquare_times x44 44) x44 in
  fsquare_times_lemma x44 44;
  assert_norm (pow2 44 = 0x100000000000);
  lemma_pow_pow_mod_mul f 0xfffffffffff 0x100000000000 0xfffffffffff;
  assert (x88 == M.pow f 0xffffffffffffffffffffff % S.prime);

  let x176 = S.fmul (fsquare_times x88 88) x88 in
  fsquare_times_lemma x88 88;
  assert_norm (pow2 88 = 0x10000000000000000000000);
  lemma_pow_pow_mod_mul f 0xffffffffffffffffffffff 0x10000000000000000000000 0xffffffffffffffffffffff;
  assert (x176 == M.pow f 0xffffffffffffffffffffffffffffffffffffffffffff % S.prime);

  let x220 = S.fmul (fsquare_times x176 44) x44 in
  fsquare_times_lemma x176 44;
  lemma_pow_pow_mod_mul f 0xffffffffffffffffffffffffffffffffffffffffffff 0x100000000000 0xfffffffffff;
  assert (x220 == M.pow f 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff % S.prime);

  let x223 = S.fmul (fsquare_times x220 3) x3 in
  fsquare_times_lemma x220 3;
  lemma_pow_pow_mod_mul f 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff 0x8 0x7;
  assert (x223 == M.pow f 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff % S.prime);

  let r0 = S.fmul (fsquare_times x223 23) x22 in
  fsquare_times_lemma x223 23;
  assert_norm (pow2 23 = 0x800000);
  lemma_pow_pow_mod_mul f 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff 0x800000 0x3fffff;
  assert (r0 == M.pow f 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff % S.prime);

  let r1 = S.fmul (fsquare_times r0 5) f in
  fsquare_times_lemma r0 5;
  assert_norm (pow2 5 = 0x20);
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff 0x20 0x1;
  assert (r1 == M.pow f 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffe1 % S.prime);

  let r2 = S.fmul (fsquare_times r1 3) x2 in
  fsquare_times_lemma r1 3;
  lemma_pow_pow_mod_mul f 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffe1 0x8 0x3;
  assert (r2 == M.pow f 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff0b % S.prime);

  let r = S.fmul (fsquare_times r2 2) f in
  fsquare_times_lemma r2 2;
  lemma_pow_pow_mod_mul f 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff0b 0x4 0x1;
  assert (r == M.pow f 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2d % S.prime)


val finv_is_finv_lemma: f:S.felem -> Lemma (finv f == S.finv f)
let finv_is_finv_lemma f =
  finv_lemma f;
  assert (finv f == M.pow f (S.prime - 2) % S.prime);
  M.lemma_pow_mod #S.prime f (S.prime - 2)
