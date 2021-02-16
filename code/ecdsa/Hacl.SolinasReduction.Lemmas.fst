module Hacl.SolinasReduction.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Spec.P256
open FStar.Mul
open Lib.Sequence

open FStar.Tactics
open FStar.Tactics.Canon

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 300"

noextract
let prime = prime256

noextract
let _uint32 = n:nat{n < pow2 32}

noextract
val c8_reduction: c8: _uint32 -> Lemma
  (c8 * pow2 256 % prime ==
   (c8 * pow2 (7 * 32) - c8 * pow2 (6 * 32) - c8 *  pow2 (3 * 32) + c8) % prime)

let c8_reduction c8 =
  calc (==) {
    c8 * pow2 256 % prime;
    == { lemma_mod_mul_distr_r c8 (pow2 256) prime }
    c8 * (pow2 256 % prime) % prime;
    == { assert_norm (pow2 256 % prime = (pow2 (7 * 32) - pow2 (6 * 32) - pow2 (3 * 32) + 1) % prime) }
    c8 * ((pow2 (7 * 32) - pow2 (6 * 32) - pow2 (3 * 32) + 1) % prime) % prime;
    == { lemma_mod_mul_distr_r c8 ((pow2 (7 * 32) - pow2 (6 * 32) - pow2 (3 * 32) + 1)) prime }
    c8 * ((pow2 (7 * 32) - pow2 (6 * 32) - pow2 (3 * 32) + 1)) % prime;
    == { _ by (canon ()) }
    (c8 * pow2 (7 * 32) - c8 * pow2 (6 * 32) - c8 * pow2 (3 * 32) + c8) % prime;
  }

noextract
val c9_reduction: c9: _uint32 -> Lemma
  (c9 * pow2 (9 * 32) % prime ==
   (-c9 * pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 * pow2 (3 * 32) + c9 * pow2 (1 * 32) + c9) % prime)

let c9_reduction c9 =
  calc (==) {
    c9 * pow2 (9 * 32) % prime;
    == { lemma_mod_mul_distr_r c9 (pow2 (9 * 32)) prime }
    c9 * (pow2 (9 * 32) % prime) % prime;
    == { assert_norm (pow2 (9 * 32) % prime = (-pow2 (6 * 32) - pow2 (4 * 32) - pow2 (3 * 32) + pow2 (1 * 32) + 1) % prime) }
    c9 * ((-pow2 (6 * 32) - pow2 (4 * 32) - pow2 (3 * 32) + pow2 (1 * 32) + 1) % prime) % prime;
    == { lemma_mod_mul_distr_r c9 (-pow2 (6 * 32) - pow2 (4 * 32) - pow2 (3 * 32) + pow2 (1 * 32) + 1) prime }
    c9 * ((-pow2 (6 * 32) - pow2 (4 * 32) - pow2 (3 * 32) + pow2 (1 * 32) + 1)) % prime;
    == { _ by (canon ()) }
    (-c9 * pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 * pow2 (3 * 32) + c9 * pow2 (1 * 32) + c9) % prime;
  }

noextract
val c10_reduction: c10: _uint32 -> Lemma
  (c10 * pow2 (10 * 32) % prime ==
  (-c10 * pow2 (7 * 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32)) % prime)

let c10_reduction c10 =
  calc (==) {
    c10 * pow2 (10 * 32) % prime;
    == { lemma_mod_mul_distr_r c10 (pow2 (10 * 32)) prime }
    c10 * (pow2 (10 * 32) % prime) % prime;
    == { assert_norm (pow2 (10 * 32) % prime = (-pow2 (7 * 32) - pow2 (5 * 32) - pow2 (4 * 32) + pow2 32 + pow2 (2 * 32)) % prime) }
    c10 * ((-pow2 (7 * 32) - pow2 (5 * 32) - pow2 (4 * 32) + pow2 32 + pow2 (2 * 32)) % prime) % prime;
    == { lemma_mod_mul_distr_r c10 (-pow2 (7 * 32) - pow2 (5 * 32) - pow2 (4 * 32) + pow2 32 + pow2 (2 * 32)) prime }
    c10 * ((-pow2 (7 * 32) - pow2 (5 * 32) - pow2 (4 * 32) + pow2 32 + pow2 (2 * 32))) % prime;
    == { _ by (canon ()) }
    (-c10 * pow2 (7 * 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32)) % prime;
  }

noextract
val c11_reduction: c11: _uint32 -> Lemma
  (c11 * pow2 (11 * 32) % prime ==
  (2 * c11 * pow2 (3 * 32) + c11 * pow2 (2 * 32) - c11 - c11 * pow2 (32 * 7) - c11 * pow2 (5 * 32)) % prime)
  
let c11_reduction c11  =  
  let open FStar.Tactics in
  let open FStar.Tactics.Canon in
  calc (==) {
    c11 * pow2 (11 * 32) % prime;
    == { lemma_mod_mul_distr_r c11 (pow2 (11 * 32)) prime }
    c11 * (pow2 (11 * 32) % prime) % prime;
    == { assert_norm (pow2 (11 * 32) % prime = (2 * pow2 (3 * 32) + pow2 (2 * 32) - 1 - pow2 (7 * 32) - pow2 (5 * 32)) % prime) }
    c11 * ((2 * pow2 (3 * 32) + pow2 (2 * 32) - 1 - pow2 (7 * 32) - pow2 (5 * 32)) % prime) % prime;
    == { lemma_mod_mul_distr_r c11 (2 * pow2 (3 * 32) + pow2 (2 * 32) - 1 - pow2 (7 * 32) - pow2 (5 * 32)) prime }
    c11 * ((2 * pow2 (3 * 32) + pow2 (2 * 32) - 1 - pow2 (7 * 32) - pow2 (5 * 32))) % prime;
    == { _ by (canon ()) }
    (2 * c11 * pow2 (3 * 32) + c11 * pow2 (2 * 32) - c11 - c11 * pow2 (32 * 7) - c11 * pow2 (5 * 32)) % prime;
   }

noextract
val c12_reduction: c12: _uint32 -> Lemma
  (c12 * pow2 (12 * 32) % prime ==
   (2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32)) % prime)

let c12_reduction c12 =
  calc (==) {
    c12 * pow2 (12 * 32) % prime;
    == { lemma_mod_mul_distr_r c12 (pow2 (12 * 32)) prime }
    c12 * (pow2 (12 * 32) % prime) % prime;
    == { assert_norm (pow2 (12 * 32) % prime == (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime) }
    c12 * ((2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime) % prime;
    == { lemma_mod_mul_distr_r c12 (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) prime }
    c12 * (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime;
    == { _ by (canon ()) }
    (2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32)) % prime;
  }

noextract
val c13_reduction: c13: _uint32 -> Lemma
  (c13 * pow2 (13 * 32) % prime ==
   (2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime)

let c13_reduction c13 =
  calc (==) {
    c13 * pow2 (13 * 32) % prime;
    == { lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime }
    c13 * (pow2 (13 * 32) % prime) % prime;
    == { assert_norm (pow2 (13 * 32) % prime == (2 * pow2 (5 * 32) + 2 * pow2 (4 * 32) + pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime) }
    c13 * ((2 * pow2 (5 * 32) + 2 * pow2 (4 * 32) + pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime) % prime;
    == { lemma_mod_mul_distr_r c13 (2 * pow2 (5 * 32) + 2 * pow2 (4 * 32) + pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 - pow2 (7 * 32)) prime }
    c13 * (2 * pow2 (5 * 32) + 2 * pow2 (4 * 32) + pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 - pow2 (7 * 32)) % prime;
    == { _ by (canon ()) }
    (2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime;
  }

noextract
val c14_reduction: c14: _uint32 -> Lemma
  (c14 * pow2 (14 * 32) % prime ==
   (2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime)

let c14_reduction c14 =
  calc (==) {
    c14 * pow2 (14 * 32) % prime;
    == { lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime }
    c14 * (pow2 (14 * 32) % prime) % prime;
    == { assert_norm (pow2 (14 * 32) % prime == (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime) }
    c14 * ((2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime) % prime;
    == { lemma_mod_mul_distr_r c14 (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) prime }
    c14 * (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime;
    == { _ by (canon ()) }
    (2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime;
  }

noextract
val c15_reduction: c15: _uint32 -> Lemma
  (c15 * pow2 (15 * 32) % prime ==
   (2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32) % prime)

let c15_reduction c15 =
  calc (==) {
    c15 * pow2 (15 * 32) % prime;
    == { lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime }
    c15 * (pow2 (15 * 32) % prime) % prime;
    == { assert_norm (pow2 (15 * 32) % prime == (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime) }
    c15 * ((2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime) % prime;
    == { lemma_mod_mul_distr_r c15 (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) prime }
    c15 * (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime;
    == { _ by (canon ()) }
    (2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32) % prime;
  }

noextract
val inside_mod: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->
  Lemma (
  (a + b + c + d + e + f + g + h + i) % prime ==
  (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime)) % prime)

let inside_mod a b c d e f g h i =
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime)) i prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (h % prime) + i) g prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + g + i) h prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + g + h + i) f prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + f + g + h + i) e prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime)  + e + f + g + h + i) d prime;
  lemma_mod_add_distr (a + (b % prime) + d + e + f + g + h + i) c prime;
  lemma_mod_add_distr (a + c+ d + e + f + g + h + i) b prime

noextract
val inside_mod1: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->
  Lemma (
    (a + 2 * b + 2 * c + d + e  - f - g - h - i) % prime ==
    ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - (h % prime) - (i % prime)) % prime)

let inside_mod1 a b c d e f g h i =
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - (h % prime)) i prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - i) h prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - h - i) g prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - g -h - i) f prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) - f - g - h - i) e prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + e - f - g - h - i) d prime;

  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime)  + d + e - f - g - h - i) (2 * (c % prime)) prime;
  lemma_mod_mul_distr_r 2 c prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime)  + d + e - f - g - h - i) (2 * c) prime;

  lemma_mod_add_distr ((a % prime) + 2 * c  + d + e - f - g - h - i) (2 * (b % prime)) prime;
  lemma_mod_mul_distr_r 2 b prime;
  lemma_mod_add_distr ((a % prime) + 2 * c  + d + e - f - g - h - i) (2 * b) prime;
  lemma_mod_add_distr (2 * b + 2 * c + d + e - f - g - h - i) a prime

noextract
val solinas_reduction_nat:
  c0_n: _uint32->
  c1_n: _uint32 ->
  c2_n: _uint32 ->
  c3_n: _uint32 ->
  c4_n: _uint32 ->
  c5_n: _uint32 ->
  c6_n: _uint32 ->
  c7_n: _uint32 ->
  c8_n: _uint32 ->
  c9_n: _uint32 ->
  c10_n: _uint32 ->
  c11_n: _uint32 ->
  c12_n: _uint32 ->
  c13_n: _uint32 ->
  c14_n: _uint32 ->
  c15_n: _uint32->
  s0: int {s0 = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32)} ->
  s1: int {s1 = c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} ->
  s2: int {s2 = c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)} ->
  s3: int {s3 = c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} ->
  s4: int {s4 = c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)} ->
  s5: int {s5 = c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32)} ->
  s6: int {s6 = c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)} ->
  s7: int {s7 = c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)} ->
  s8: int {s8 = c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) + c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32)} ->
  n: int {n = s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8} ->
Lemma (n % prime == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)) % prime)

let solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0 s1 s2 s3 s4 s5 s6 s7 s8 n =
  assert_by_tactic (2 * (c11 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32)) == 2 * c11 * pow2 (3 * 32) + 2 * c12 * pow2 (4 * 32) + 2 * c13 * pow2 (5 * 32) + 2 * c14 * pow2 (6 * 32) + 2 * c15 * pow2 (7 * 32)) canon;
  assert_by_tactic (2 * (c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5 * 32) + c15 * pow2 (6 * 32)) = 2 * c12 * pow2 (3 * 32) + 2 * c13 * pow2 (4 * 32) + 2 * c14 * pow2 (5* 32) + 2* c15 * pow2 (6 * 32)) canon;

  let a_ =  c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) in
  let c8_ = c8 * pow2 (7 * 32) - c8 * pow2 (6 * 32) - c8 * pow2 (3 * 32) + c8 in
  let c9_ = - c9 * pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 * pow2 (3 * 32) + c9 * pow2 32 + c9 in
  let c10_ = -c10 * pow2 (7 * 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32) in
  let c11_ = 2 * c11 * pow2 96 + c11 * pow2 64 - c11 - c11 * pow2 (7 * 32) - c11 * pow2 (5 * 32) in
  let c12_ = 2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32) in
  let c13_ = 2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32) in
  let c14_ = 2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14  in
  let c15_ = 2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32 in

  inside_mod a_ c8_ c9_ c10_ c11_ c12_ c13_ c14_ c15_;
  c8_reduction c8;
  c9_reduction c9;
  c10_reduction c10;
  c11_reduction c11;
  c12_reduction c12;
  c13_reduction c13;
  c14_reduction c14;
  c15_reduction c15;

  inside_mod a_ (c8 * pow2 (8 * 32)) (c9 * pow2 (9 * 32)) (c10 * pow2 (10 * 32)) (c11 * pow2 (11 * 32)) (c12 * pow2 (12 * 32)) (c13 * pow2 (13 * 32)) (c14 * pow2 (14 * 32)) (c15 * pow2 (15 * 32))

noextract
val solinas_reduction_mod:
  c0_n: _uint32->
  c1_n: _uint32 ->
  c2_n: _uint32 ->
  c3_n: _uint32 ->
  c4_n: _uint32 ->
  c5_n: _uint32 ->
  c6_n: _uint32 ->
  c7_n: _uint32 ->
  c8_n: _uint32 ->
  c9_n: _uint32 ->
  c10_n: _uint32 ->
  c11_n: _uint32 ->
  c12_n: _uint32 ->
  c13_n: _uint32 ->
  c14_n: _uint32 ->
  c15_n: _uint32->
  s0: int {s0 = (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32)) % prime} ->
  s1: int {s1 = (c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) % prime} ->
  s2: int {s2 = (c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)) % prime} ->
  s3: int {s3 = (c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) % prime} ->
  s4: int {s4 = (c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)) % prime} ->
  s5: int {s5 = (c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32)) % prime} ->
  s6: int {s6 = (c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)) % prime} ->
  s7: int {s7 = (c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)) % prime} ->
  s8: int {s8 = (c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) + c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32)) % prime} ->
  n: int {n = (s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8) % prime} ->
Lemma (n % prime == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)) % prime)

let solinas_reduction_mod c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0 s1 s2 s3 s4 s5 s6 s7 s8 n  =
    assert(n =  (s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8) % prime);
  let s0_ = c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) in
  let s1_ = c11 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) in
  let s2_ = c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5* 32) + c15 * pow2 (6 * 32) in
  let s3_ = c8 + c9 * pow2 32 + c10 * pow2 (2 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) in
  let s4_ = c9 + c10 * pow2 32 + c11 * pow2 (2 * 32) + c13 * pow2 (3 * 32) + c14 * pow2 (4 * 32) + c15 * pow2 (5 * 32) + c13 * pow2 (6 * 32) + c8 * pow2 (7 * 32) in
  let s5_ = c11 + c12 * pow2 32 + c13 * pow2 (2 * 32) + c8 * pow2 (6 * 32) + c10 * pow2 (7 * 32) in
    assert(- (s5_ % prime) = - s5);
  let s6_ = c12 + c13 * pow2 32 + c14 * pow2 (2 * 32) + c15 * pow2 (3 * 32) + c9 * pow2 (6 * 32) + c11 * pow2 (7 * 32) in
    assert(- (s6_ % prime) = - s6);
  let s7_ = c13 + c14 * pow2 32 + c15 * pow2 (2 * 32) + c8 * pow2 (3 * 32) + c9 * pow2 (4 * 32) + c10 * pow2 (5 * 32) + c12 * pow2 (7 * 32) in
  let s8_ = c14 + c15 * pow2 32 + c9 * pow2 (3 * 32) + c10 * pow2 (4* 32) + c11 * pow2 (5 * 32) + c13 * pow2 (7 * 32) in
  let n_ = s0_ + 2 * s1_ + 2 * s2_ + s3_ + s4_ - s5_ - s6_ - s7_ - s8_ in
  solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ n_;

     assert(s0 = s0_ % prime);
     assert(s1 = s1_ % prime);
     assert(s2 = s2_ % prime);
     assert(s3 = s3_ % prime);
     assert(s4 = s4_ % prime);
     assert(s5 = s5_ % prime);
     assert(s6 = s6_ % prime);
     assert(s7 = s7_ % prime);
     assert(s8 = s8_ % prime);

  assert(n_ % prime == (c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 256 + c9 * pow2 288 + c10 * pow2 (10 * 32)  + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32)) % prime);

  assert(n_ % prime =  (s0_ + 2 * s1_ + 2 * s2_ + s3_ + s4_ - s5_ - s6_ - s7_ - s8_) % prime);
  assert(n =  (s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8) % prime);
  assert(n = ((s0_ % prime) + 2 * (s1_ % prime) + 2 * (s2_ % prime) + s3_ % prime + s4_ % prime - (s5_ % prime) - (s6_ % prime) - (s7_ % prime) - (s8_ % prime)) % prime);

  inside_mod1 s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ ;

    assert(n = (s0_ + 2 * s1_ + 2 * s2_ + s3_ + s4_ - s5_ - s6_ - s7_ - s8_) % prime);
    assert(n = ((s0_ + 2 * s1_ + 2 * s2_ + s3_ + s4_ - s5_ - s6_ - s7_ - s8_) % prime));
    assert(n = n_ % prime);
    assert(n =  (c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 256 + c9 * pow2 288 + c10 * pow2 (10 * 32)  + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32)) % prime);
    assert(n % prime =  ((c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 256 + c9 * pow2 288 + c10 * pow2 (10 * 32)  + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32)) % prime) % prime);
    small_mod ((c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 256 + c9 * pow2 288 + c10 * pow2 (10 * 32)  + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32)) % prime) prime


val reduce_brackets: r0: nat -> r1: nat -> r2: nat -> r3: nat -> r4: nat -> r5: nat -> r6: nat -> r7: nat -> r8: nat ->
  Lemma (
    (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime ==
    (r0 + 2 * r1 + 2 * r2 + r3 + r4 - r5  - r6 - r7 - r8) % prime)


let reduce_brackets r0 r1 r2 r3 r4 r5 r6 r7 r8  =
  let n = (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime in

  lemma_mod_add_distr (- r8) ((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) prime;

  lemma_mod_add_distr (-r7 - r8) (((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) prime;

    assert(n == (((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6 - r7 - r8) % prime);

  lemma_mod_add_distr (-r6 - r7 - r8)  ((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) prime;

    assert(n == ((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5 - r6 - r7 - r8) % prime);


  lemma_mod_add_distr (-r5 -r6 - r7 - r8)  (((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) prime;

   assert(n == (((((r0 + ((2 * r1) % prime)) % prime +  ((2 * r2) % prime)) % prime) + r3) % prime + r4 - r5 - r6 - r7 - r8) % prime);

  lemma_mod_add_distr (r4 -r5 -r6 - r7 - r8)  ((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) prime;

   assert(n == ((((r0 + ((2 * r1) % prime)) % prime +  ((2 * r2) % prime)) % prime) + r3 + r4 - r5 - r6 - r7 - r8) % prime);

  lemma_mod_add_distr (r3 + r4 - r5 - r6 - r7 - r8) (((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime))) prime;

   assert(n == ((r0 + ((2 * r1) % prime)) % prime +  ((2 * r2) % prime) + r3 + r4 - r5 - r6 - r7 - r8) % prime);

  lemma_mod_add_distr ((r0 + ((2 * r1) % prime)) % prime + r3 + r4 - r5 - r6 - r7 - r8) (2 * r2) prime;

  assert(n == ((r0 + ((2 * r1) % prime)) % prime +  (2 * r2) + r3 + r4 - r5 - r6 - r7 - r8) % prime);

  lemma_mod_add_distr ((2 * r2) + r3 + r4 - r5 - r6 - r7 - r8) (r0 + ((2 * r1) % prime)) prime;

 assert(n == (r0 + ((2 * r1) % prime) +  (2 * r2) + r3 + r4 - r5 - r6 - r7 - r8) % prime);

 lemma_mod_add_distr (r0  +  (2 * r2) + r3 + r4 - r5 - r6 - r7 - r8) (2 * r1) prime;

 assert(n == (r0 + (2 * r1) +  (2 * r2) + r3 + r4 - r5 - r6 - r7 - r8) % prime)
