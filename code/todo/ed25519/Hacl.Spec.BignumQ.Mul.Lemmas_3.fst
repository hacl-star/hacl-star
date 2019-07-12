module Hacl.Spec.BignumQ.Mul.Lemmas_3

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.UInt64
open Hacl.Spec.BignumQ.Eval

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 5"

private
let u56 = x:t{v x < 0x100000000000000}

private
let lemma_distr_4 x a b c d : Lemma (x * (a + b + c + d) = x * a + x * b + x * c + x * d)
  = ()

private
let lemma_distr_5 x a b c d e : Lemma (x * (a + b + c + d + e) = x * a + x * b + x * c + x * d + x * e)
 = ()

val lemma_mod_264:
  x0:u56 -> x1:u56 -> x2:u56 -> x3:u56 -> x4:u56 -> x5:u56 -> x6:u56 -> x7:u56 -> x8:u56 -> x9:u56 ->
  Lemma ((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4
         + p5 * v x5 + p6 * v x6 + p7 * v x7 + p8 * v x8 + p9 * v x9) % pow2 264
         = v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * (v x4 % 0x10000000000))
let lemma_mod_264 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 16 = 0x10000);
  assert_norm(pow2 72 = 0x1000000000000000000);
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  assert_norm(pow2 184 = 0x10000000000000000000000000000000000000000000000);
  assert_norm(pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000);
  lemma_distr_5 0x1000000000000000000000000000000000000000000000000000000000000000000
               (0x10000 * v x5) (0x1000000000000000000 * v x6) (0x100000000000000000000000000000000 * v x7) (0x10000000000000000000000000000000000000000000000 * v x8) (0x1000000000000000000000000000000000000000000000000000000000000 * v x9);
  Math.Lemmas.lemma_mod_plus (v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4) (0x10000 * v x5 + 0x1000000000000000000 * v x6 + 0x100000000000000000000000000000000 * v x7 + 0x10000000000000000000000000000000000000000000000 * v x8 + 0x1000000000000000000000000000000000000000000000000000000000000 * v x9) 0x1000000000000000000000000000000000000000000000000000000000000000000;
  assert((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4
         + p5 * v x5 + p6 * v x6 + p7 * v x7 + p8 * v x8 + p9 * v x9) % pow2 264
         = (v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4) % pow2 264);
  Math.Lemmas.lemma_mod_plus_distr_l (p4 * v x4) (v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3) 0x1000000000000000000000000000000000000000000000000000000000000000000;
  assert_norm(p4 = pow2 224);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v x4) 264 224;
  Math.Lemmas.modulo_lemma (v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * (v x4 % 0x10000000000)) (pow2 264)

val lemma_div_224:
  x0:u56 -> x1:u56 -> x2:u56 -> x3:u56 -> x4:u56 -> x5:u56 -> x6:u56 -> x7:u56 -> x8:u56 -> x9:u56 ->
  Lemma ((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4
         + p5 * v x5 + p6 * v x6 + p7 * v x7 + p8 * v x8 + p9 * v x9) / pow2 224
         = v x4 + p1 * v x5 + p2 * v x6 + p3 * v x7 + p4 * v x8 + p5 * v x9)
let lemma_div_224 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
  assert_norm(pow2 56  = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 280 = 0x10000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 336 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 392 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 448 = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


val lemma_div_24:
  x0:u56 -> x1:u56 -> x2:u56 -> x3:u56 -> x4:u56 -> x5:UInt64.t{v x5 < 0x100} ->
  Lemma ((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4 + p5 * v x5) / pow2 24
         = v x0 / pow2 24 + (v x1 % pow2 24) * pow2 32
           + p1 * (v x1 / pow2 24 + (v x2 % pow2 24) * pow2 32)
           + p2 * (v x2 / pow2 24 + (v x3 % pow2 24) * pow2 32)
           + p3 * (v x3 / pow2 24 + (v x4 % pow2 24) * pow2 32)
           + p4 * (v x4 / pow2 24 + v x5 * pow2 32))
let lemma_div_24 x0 x1 x2 x3 x4 x5 =
  assert_norm(pow2 24 = 0x1000000);
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 56  = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  Math.Lemmas.lemma_div_mod (v x0) (pow2 24);
  lemma_distr_5 0x1000000 (v x0 / pow2 24) (0x100000000 * v x1) (0x10000000000000000000000 * v x2) (0x1000000000000000000000000000000000000 * v x3) (0x100000000000000000000000000000000000000000000000000 * v x4);
  Math.Lemmas.division_addition_lemma (v x0 % pow2 24) (pow2 24) ((v x0 / pow2 24)+(0x100000000 * v x1)+(0x10000000000000000000000 * v x2)+(0x1000000000000000000000000000000000000 * v x3)+(0x100000000000000000000000000000000000000000000000000 * v x4)+(0x10000000000000000000000000000000000000000000000000000000000000000 * v x5));
  Math.Lemmas.small_division_lemma_1 (v x0 % pow2 24) (pow2 24);
  assert((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4) / pow2 24
    = (v x0 / pow2 24 + (0x100000000 * v x1)+(0x10000000000000000000000 * v x2)+(0x1000000000000000000000000000000000000 * v x3)+(0x100000000000000000000000000000000000000000000000000 * v x4)));
    Math.Lemmas.lemma_div_mod (v x1) (pow2 24);
    Math.Lemmas.lemma_div_mod (v x2) (pow2 24);
    Math.Lemmas.lemma_div_mod (v x3) (pow2 24);
    Math.Lemmas.lemma_div_mod (v x4) (pow2 24);
    Math.Lemmas.lemma_div_mod (v x5) (pow2 24)


val lemma_div_40:
  x0:u56 -> x1:u56 -> x2:u56 -> x3:u56 -> x4:u56 -> x5:UInt64.t{v x5 < 0x1000000} ->
  Lemma ((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4 + p5 * v x5) / pow2 40
         = v x0 / pow2 40 + (v x1 % pow2 40) * pow2 16
           + p1 * (v x1 / pow2 40 + (v x2 % pow2 40) * pow2 16)
           + p2 * (v x2 / pow2 40 + (v x3 % pow2 40) * pow2 16)
           + p3 * (v x3 / pow2 40 + (v x4 % pow2 40) * pow2 16)
           + p4 * (v x4 / pow2 40 + v x5 * pow2 16))
let lemma_div_40 x0 x1 x2 x3 x4 x5 =
  assert_norm(pow2 16 = 0x10000);
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 56  = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  Math.Lemmas.lemma_div_mod (v x0) (pow2 40);
  lemma_distr_5 0x1000000 (v x0 / pow2 40) (0x10000 * v x1) (0x1000000000000000000 * v x2) (0x100000000000000000000000000000000 * v x3) (0x10000000000000000000000000000000000000000000000 * v x4);
  Math.Lemmas.division_addition_lemma (v x0 % pow2 40) (pow2 40) ((v x0 / pow2 40)+(0x10000 * v x1)+(0x1000000000000000000 * v x2)+(0x100000000000000000000000000000000 * v x3)+(0x10000000000000000000000000000000000000000000000 * v x4)+(0x1000000000000000000000000000000000000000000000000000000000000 * v x5));
  Math.Lemmas.small_division_lemma_1 (v x0 % pow2 40) (pow2 40);
  assert((v x0 + p1 * v x1 + p2 * v x2 + p3 * v x3 + p4 * v x4 + p5 * v x5) / pow2 40
    = (v x0 / pow2 40 + (0x10000 * v x1)+(0x1000000000000000000 * v x2)+(0x100000000000000000000000000000000 * v x3)+(0x10000000000000000000000000000000000000000000000 * v x4)+(0x1000000000000000000000000000000000000000000000000000000000000 * v x5)));
    Math.Lemmas.lemma_div_mod (v x1) (pow2 40);
    Math.Lemmas.lemma_div_mod (v x2) (pow2 40);
    Math.Lemmas.lemma_div_mod (v x3) (pow2 40);
    Math.Lemmas.lemma_div_mod (v x4) (pow2 40);
    Math.Lemmas.lemma_div_mod (v x5) (pow2 40)
