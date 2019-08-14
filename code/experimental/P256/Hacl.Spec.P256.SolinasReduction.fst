
module Hacl.Spec.P256.SolinasReduction

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Definitions
open FStar.Mul
open Lib.Sequence

open Hacl.Spec.P256.Core

let prime = prime256

let _uint32 = n: nat {n < pow2 32}

inline_for_extraction noextract
val get_high_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a / (pow2 32)})

let get_high_part a = 
  to_u32(shift_right a (size 32))



inline_for_extraction noextract
val get_low_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a % (pow2 32)}) 

let get_low_part a = to_u32 a



val lemma_xor_zero: low: uint64{uint_v (get_high_part low) ==  0} -> high: uint64{uint_v (get_low_part high) == 0} ->  Lemma (uint_v (logxor low high) = uint_v high * pow2 32 + uint_v low)

let lemma_xor_zero low high = 
  assert(uint_v low = uint_v (get_low_part low));
  assert(uint_v high = uint_v (get_high_part high) * pow2 32);
  admit()

val store_high_low_u: high: uint32 -> low: uint32 -> Tot (r: uint64 {uint_v r = uint_v high * pow2 32+ uint_v low})


let store_high_low_u high low = 
  let as_uint64_high = to_u64 high in 
  let as_uint64_high = Lib.IntTypes.shift_left as_uint64_high (size 32) in 
  let as_uint64_low = to_u64 low in
  lemma_xor_zero as_uint64_low as_uint64_high;
  logxor as_uint64_low as_uint64_high



val c8_reduction: c8: _uint32  -> 
  Lemma((c8 * pow2 256) % prime == (c8 * pow2 (7 * 32) - c8 *  pow2 (6 * 32) - c8 *  pow2 (3 * 32) + c8) % prime)

let c8_reduction c8 = 
  assert_norm(pow2 256 % prime = pow2 224 - pow2 192 - pow2 96 + 1);
  lemma_mod_mul_distr_r c8 (pow2 256) prime;
  lemma_mod_mul_distr_r c8 (pow2 224 - pow2 192 - pow2 96 + 1) prime


val c9_reduction: c9: _uint32 -> 
  Lemma (c9 * pow2 (9 * 32) % prime == (- c9 *  pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 *  pow2 (3 * 32) + c9 * pow2 (1 * 32) + c9) % prime)

let c9_reduction c9 = 
  lemma_mod_mul_distr_r c9 (pow2 288) prime;
  assert_norm (pow2 288 % prime == (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) % prime);
  lemma_mod_mul_distr_r c9 (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) prime


val c10_reduction: c10: _uint32 -> Lemma (c10 * pow2 (10* 32) % prime ==  (- c10 * pow2 (7 * 32) -c10 *  pow2 (5*32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32)) % prime)

let c10_reduction c10 = 
  lemma_mod_mul_distr_r c10 (pow2 (32 * 10)) prime;
  assert_norm (pow2 (10 * 32) % prime = (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64)% prime);
  lemma_mod_mul_distr_r c10 (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64) prime


val c11_reduction: c11: _uint32  -> Lemma (c11 * pow2 (11 * 32) % prime == (2 * c11 * pow2 (3 * 32) + c11 * pow2 (2 * 32) - c11 - c11 * pow2 (32 * 7) - c11 * pow2 (5 * 32)) % prime)

let c11_reduction c11  = 
  assert_norm((pow2 (11 * 32) % prime == (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) % prime));
  lemma_mod_mul_distr_r c11 (pow2 (11 * 32)) prime;
  lemma_mod_mul_distr_r c11 (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) prime


val c12_reduction: c12: _uint32-> Lemma (c12 * pow2 (12 * 32) % prime == (2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32)) % prime)

let c12_reduction c12 = 
  assert_norm (pow2 (12 * 32) % prime == (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32))% prime);
  lemma_mod_mul_distr_r c12 (pow2 (12 * 32)) prime;
  lemma_mod_mul_distr_r c12 (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) prime


val c13_reduction: c13: _uint32-> Lemma (c13 * pow2 (13 * 32) % prime == (2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 *  pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 *  pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime)

let c13_reduction c13 = 
  assert_norm (pow2 (13 * 32) % prime == (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) % prime);
  lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime;
  lemma_mod_mul_distr_r c13 (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) prime


val c14_reduction: c14: _uint32 -> Lemma (c14 * pow2 (14 * 32) % prime == (2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime)

let c14_reduction c14 = 
  assert_norm (pow2 (14 * 32) % prime == (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime);
  lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime;
  lemma_mod_mul_distr_r c14 (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) prime


val c15_reduction: c15: _uint32 -> Lemma (c15 * pow2 (15 * 32) % prime == (2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32)% prime)

let c15_reduction c15 = 
  assert_norm (pow2 (15 * 32) % prime ==  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime);
  lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime;
  lemma_mod_mul_distr_r c15  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) prime


val inside_mod: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->
  Lemma (
  (a + b + c + d + e + f + g + h + i) % prime == 
  (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime)) % prime)

let inside_mod a b c d e f g h i = 
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime)) i prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + h + i) g prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + g + h + i) f prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + f + g + h + i) e prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime)  + e + f + g + h + i) d prime;
  lemma_mod_add_distr (a + (b % prime) + d + e + f + g + h + i) c prime;
  lemma_mod_add_distr (a + c+ d + e + f + g + h + i) b prime


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
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

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

#reset-options "--z3refresh --z3rlimit 100"

(* slightly suspicious lemma *)
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
  inside_mod1 s0_  s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_


val reduce_brackets: r0: nat -> r1: nat -> r2: nat -> r3: nat -> r4: nat -> r5: nat -> r6: nat -> r7: nat -> r8: nat ->  
  Lemma (
    (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime == 
    (r0 + 2 * r1 + 2 * r2 + r3 + r4 - r5  - r6 - r7 - r8) % prime)

let reduce_brackets r0 r1 r2 r3 r4 r5 r6 r7 r8  =
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let n = (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime in 
  lemma_mod_add_distr (- r8) ((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) prime;
  lemma_mod_add_distr (-r7 - r8) (((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) prime;
  lemma_mod_add_distr (-r6 - r7 - r8)  ((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) prime;
  lemma_mod_add_distr (-r5 -r6 - r7 - r8)  (((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) prime;
  lemma_mod_add_distr (r4 -r5 -r6 - r7 - r8)  ((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) prime;
  lemma_mod_add_distr (r3 + r4 - r5 - r6 - r7 - r8) (((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) prime;

  let t0 = r3 + r4 - r5 - r6 - r7 - r8 in 
  let l0 = (r0 + (2 * r1 % prime)) % prime in 
  
  assert(n == (l0 + (2 * r2 % prime) + t0) % prime);
  assert_by_tactic ((l0 + (2 * r2 % prime) + t0) == ((l0 + t0) + (2 * r2 % prime))) canon;
  lemma_mod_add_distr (l0 + t0) (2 * r2 % prime) prime;
  lemma_mod_mul_distr_r 2 r2 prime;
  lemma_mod_add_distr (l0 + t0) (2 * r2) prime;
  let t1 = 2 * r2 + r3 + r4 - r5 - r6 - r7 - r8  in 
  let l1 = r0 + (2 * r1 % prime) in  
  lemma_mod_add_distr t1 l1 prime;
  lemma_mod_add_distr (r0 + t1) (2 * r1 % prime) prime;
  lemma_mod_mul_distr_r 2 r1 prime;
  lemma_mod_add_distr (r0 + t1) (2 * r1) prime
