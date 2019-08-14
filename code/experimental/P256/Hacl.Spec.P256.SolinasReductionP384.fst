module Hacl.Spec.P256.SolinasReductionP384

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open Lib.Sequence


#reset-options " --z3rlimit 300 "

let prime:pos =
  assert_norm (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 0);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1

val c12_reduction: c12: nat{c12 < pow2 32} -> Lemma ((c12 + c12 * pow2 (3 * 32) + c12 * pow2 (4 * 32)  - c12 * pow2 32) % prime ==
c12 * pow2 (12 * 32) % prime)

let c12_reduction c12 = 
    assert_norm (pow2 (12 * 32) % prime = pow2 128 + pow2 96 - pow2 32 + 1);
    lemma_mod_mul_distr_r c12 (pow2 (12 * 32)) prime;
    lemma_mod_mul_distr_r c12 (pow2 (4 * 32) + pow2 (3 * 32) - pow2 32 + 1) prime


val c13_reduction: c13: nat {c13 < pow2 32} -> Lemma ((c13 * pow2 32 + c13 * pow2 (4 * 32) + c13 * pow2 (5 * 32) - c13 * pow2(2 *32)) % prime == c13 * pow2 (13 * 32) % prime)

let c13_reduction c13 =
  assert_norm (pow2 (13 * 32) % prime = pow2 160 + pow2 128 - pow2 64 + pow2 32);
  lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime;
  lemma_mod_mul_distr_r c13 (pow2 32 + pow2 (4 * 32) + pow2 (5 * 32) - pow2 (2 * 32)) prime


val c14_reduction: c14 : nat {c14 < pow2 32} -> Lemma ((c14 * pow2 (2 * 32) + c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) - c14 * pow2 (3 * 32)) % prime == c14 * pow2 (14 * 32) % prime)

#reset-options "--z3refresh --z3rlimit 300"

let c14_reduction c14 = 
  assert_norm (pow2 (14 * 32) % prime == pow2 (2 * 32) + pow2 (5 * 32) + pow2 (6 * 32) - pow2 (3 * 32));
  lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime


val c15_reduction: c15: nat {c15 < pow2 32} -> Lemma ((c15 * pow2 (3 * 32) + c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) - c15 * pow2 (4 * 32)) % prime == c15 * pow2 (15 * 32) % prime)

let c15_reduction c15 = 
  assert_norm (pow2 (15 * 32) % prime = pow2 (3 * 32) + pow2 (6 * 32) + pow2 (7 * 32) - pow2 (4 * 32));
  lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime


val c16_reduction: c16: nat {c16 < pow2 32} -> Lemma ((c16 * pow2 (4 * 32) + c16 * pow2 (7 * 32) + c16 * pow2 (8 * 32) - c16 * pow2 (5 * 32)) % prime == c16 * pow2 (16 * 32) % prime)

let c16_reduction c16 = 
  assert_norm(pow2 (16 * 32) % prime = pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32));
  lemma_mod_mul_distr_r c16 (pow2 (16 * 32)) prime;
    assert(c16 * pow2 (16 * 32) % prime == c16 * (pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32))% prime);
  lemma_mod_mul_distr_r c16 (pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32)) prime


val c17_reduction: c17: nat {c17 < pow2 32} -> Lemma ((c17 * pow2 (5 * 32) + c17 * pow2 (8 * 32) + c17 * pow2 (9 * 32) - c17 * pow2 (6 * 32)) % prime == c17 * pow2 (17 * 32) % prime)

let c17_reduction c17 = 
  assert_norm (pow2 (17 * 32) % prime = pow2 (5 * 32) + pow2 (8 * 32) + pow2 (9 * 32) - pow2 (6 * 32));
  lemma_mod_mul_distr_r c17 (pow2 (17 * 32)) prime;
    assert(c17 * pow2 (17 * 32) % prime == c17 * (pow2 (5 * 32) + pow2 (8 * 32) + pow2 (9 * 32) - pow2 (6 * 32)) % prime);
  lemma_mod_mul_distr_r c17 (pow2 (5 * 32) + pow2 (8 * 32) + pow2 (9 * 32) - pow2 (6 * 32)) prime


val c18_reduction: c18: nat {c18 < pow2 32} -> Lemma ((c18 * pow2 (6 * 32) + c18 * pow2 (9 * 32) + c18 * pow2 (10 * 32) - c18 * pow2 (7 * 32))  % prime == c18 * pow2 (18 * 32) % prime)

let c18_reduction c18 = 
  assert_norm (pow2 (18 * 32) % prime = pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32));
  lemma_mod_mul_distr_r c18 (pow2 (18 * 32)) prime;
    assert(c18 * pow2 (18 * 32) % prime == c18 * (pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) % prime);
  lemma_mod_mul_distr_r c18 (pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) prime


val c19_reduction: c19: nat {c19 < pow2 32} -> Lemma ((c19 * pow2 (7 * 32) + c19 * pow2 (10 * 32) + c19 * pow2 (11 * 32) - c19 * pow2 (8 * 32)) % prime == c19 * pow2 (19 * 32) % prime)

let c19_reduction c19 = 
  assert_norm (pow2 (19 * 32) % prime = pow2 (7 * 32) + pow2 (10 * 32) + pow2 (11 * 32) - pow2 (8 * 32));
  lemma_mod_mul_distr_r c19 (pow2 (19 * 32)) prime;
    assert(c19 * pow2 (19 * 32) % prime == c19 * (pow2 (7 * 32) + pow2 (10 * 32) + pow2 (11 * 32) - pow2 (8 * 32)) % prime);
  lemma_mod_mul_distr_r c19 (pow2 (7 * 32) + pow2 (10 * 32) + pow2 (11 * 32) - pow2 (8 * 32)) prime


val c20_reduction: c20: nat {c20 < pow2 32} -> Lemma ((c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 32) % prime == c20 * pow2 (20 * 32) % prime)

let c20_reduction c20 =
  assert_norm (pow2 (20 * 32) % prime == pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 32 - pow2 (9 * 32));
  
  lemma_mod_mul_distr_r c20 (pow2 (20 * 32)) prime;
    assert(c20 * pow2 (20 * 32) % prime == c20 * (pow2 (20 * 32) % prime) % prime);
    assert(c20 * pow2 (20 * 32) % prime == c20 *  (pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 32 - pow2 (9 * 32)) % prime);
    assert(c20 * pow2 (20 * 32) % prime == (c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 32) % prime)


val c21_reduction: c21: nat {c21 < pow2 32} -> Lemma ((2 * c21 * pow2 (4 * 32) + c21 * pow2 (9 * 32) + c21 + c21 * pow2 (5 * 32) + c21 * pow2 (3 * 32) - c21 * pow2 (2 * 32) - c21 * pow2 (10 * 32)) % prime == c21 * pow2 (21 * 32) % prime)

let c21_reduction c21 = 
    assert_norm (pow2 (21 * 32) % prime = (2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (2 * 32) - pow2 (10 * 32)) % prime);
    lemma_mod_mul_distr_r c21 (pow2 (21 * 32)) prime;
    lemma_mod_mul_distr_r c21 (2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (2 * 32) - pow2 (10 * 32)) prime


val c22_reduction: c22: nat {c22 < pow2 32} -> Lemma ((2 * c22 * pow2 (5 * 32) + c22 * pow2 (10 * 32) + c22 * pow2 32 + c22 * pow2 (6 * 32) + c22 * pow2 (4 * 32) - c22 * pow2 (11 * 32) - c22 * pow2 (3 * 32)) % prime == c22 * pow2 (22 * 32) % prime)

let c22_reduction c22 = 
  assert_norm (pow2 (22 * 32) % prime = (2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 32 +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) -  pow2 (3 * 32)) % prime);
  lemma_mod_mul_distr_r c22 (pow2 (22 * 32)) prime;
  assert(c22 * pow2 (22 * 32) % prime == c22 * (pow2 (22 * 32) % prime) % prime);
  lemma_mod_mul_distr_r c22 (2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 32 +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) - pow2 (3 * 32)) prime


val c23_reduction: c23: nat {c23 < pow2 32} -> Lemma ((2 * c23 * pow2 (6 * 32) + c23 * pow2 (11 * 32) + c23 * pow2 (2 * 32) + c23 * pow2 32 + c23 * pow2 (7 * 32) + c23 * pow2 (5 * 32) - c23 - c23 * pow2 (4 * 32) - c23 * pow2 (3 * 32) - c23 * pow2 (4 * 32)) % prime == c23 * pow2 (23 * 32) % prime)

let c23_reduction c23 = 
  assert_norm (pow2 (23 * 32) % prime = (2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 32 + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) - pow2 (3 * 32) - pow2 (4 * 32)) % prime);
  lemma_mod_mul_distr_r c23 (pow2 (23 * 32)) prime;
  lemma_mod_mul_distr_r c23 (2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 32 + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) - pow2 (3 * 32) - pow2 (4 * 32)) prime


assume val inside_mod: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->j: int -> k: int -> l: int -> m: int -> Lemma (
  (a + b + c + d + e + f + g + h + i + j + k + l + m) % prime == 
  (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + (l % prime) + (m % prime)) % prime)


#reset-options " --z3rlimit 500 "

val solaris_reduction384: c0 : nat{c0 < pow2 32}  -> c1 : nat {c1 < pow2 32} ->  c2: nat {c2 < pow2 32} -> c3 : nat {c3 < pow2 32} ->  c4 : nat {c4 < pow2 32} ->  c5 : nat {c5 < pow2 32} ->  c6 : nat {c6 < pow2 32} ->  c7 : nat {c7 < pow2 32} ->  c8 : nat {c8 < pow2 32} ->  c9 : nat {c9 < pow2 32} ->  c10 : nat {c0 < pow2 32} ->  c11 : nat {c11 < pow2 32} ->  c12: nat {c12 < pow2 32} ->  c13 : nat {c13 < pow2 32} ->  c14 : nat {c14 < pow2 32} ->  c15 : nat {c15 < pow2 32} ->  c16 : nat {c16 < pow2 32} ->  c17 : nat {c17 < pow2 32} ->  c18 : nat {c18 < pow2 32} ->  c19 : nat {c19 < pow2 32} ->  c20 : nat {c20 < pow2 32} ->  c21 : nat {c21 < pow2 32} ->  c22 : nat {c22 < pow2 32}->  c23 : nat {c23 < pow2 32} ->
s0 : int{s0 = c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32)} ->
s1 : int{s1 = c21 * pow2 (4 * 32) + c22 * pow2 (5 * 32) + c23 * pow2 (6 * 32)} -> 
s2 : int {s2 = c12 + c13 * pow2 (1 * 32) + c14 * pow2 (2 * 32) + c15 * pow2 (3 * 32) + c16 * pow2 (4 * 32) + c17 * pow2 (5 * 32) + c18 * pow2 (6 * 32) + c19 * pow2 (7 * 32) + c20 * pow2 (8 * 32) + c21 * pow2 (9 * 32) + c22 * pow2 (10 * 32) + c23 * pow2 (11 * 32)} -> 
s3:int {s3 = c21 + c22 * pow2 32 + c23 * pow2 (2 * 32) + c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5 * 32) + c15 * pow2 (6 * 32) + c16 * pow2 (7 * 32) + c17 * pow2 (8 * 32) + c18 * pow2 (9 * 32) + c19 * pow2 (10 * 32) + c20 * pow2 (11 * 32)} ->
s4: int {s4 = c23 * pow2 32 + c20 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c16 * pow2 (8 * 32) + c17 * pow2 (9 * 32) + c18 * pow2 (10 * 32) + c19 * pow2 (11 * 32)} ->
s5 : int {s5 = c20 * pow2 (4 * 32) + c21 * pow2 (5 * 32) + c22 * pow2 (6 * 32) + c23 * pow2 (7 * 32)} ->
s6 : int {s6 = c20 + c21 * pow2 (3 * 32) + c22 * pow2 (4 * 32) + c23 * pow2 (5 * 32)} ->
s7 : int {s7 = c23 + c12 * pow2 32 + c13 * pow2 (2 * 32) + c14 * pow2 (3 * 32) + c15 * pow2 (4 * 32) + c16 * pow2 (5 * 32) + c17 * pow2 (6 * 32) + c18 * pow2 (7 * 32) + c19 * pow2 (8 * 32) + c20 * pow2 (9 * 32) + c21 * pow2 (10 * 32) + c22 * pow2 (11 * 32)} ->
s8: int {s8 = c20 * pow2 32 + c21 * pow2 (2 * 32 ) + c22 * pow2 (3 * 32) + c23 * pow2 (4 * 32)} ->
s9: int {s9 = c23 * pow2 (3 * 32) + c23 * pow2 (4 * 32)} ->
n: nat {n = (s0 + 2 * s1 + s2 + s3 + s4 + s5 + s6 - s7 - s8 - s9) % prime} -> 
Lemma (n  == (c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32) + c16 * pow2 (16 * 32) + c17 * pow2 (17 * 32) + c18 * pow2 (18 * 32) + c19 * pow2 (19 * 32) + c20 * pow2 (20 * 32) + c21 * pow2 (21 * 32) + c22 * pow2 (22 * 32) + c23 * pow2 (23 * 32)) % prime)

#reset-options "--z3refresh --z3rlimit 500"

let solaris_reduction384 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 n = 
  let open FStar.Tactics in
  let open FStar.Tactics.Canon in 

  assert_by_tactic (2 * (c21 * pow2 (4 * 32) + c22 * pow2 (5 * 32) + c23 * pow2 (6 * 32)) == 2 * c21 * pow2 (4 * 32) + 2 * c22 * pow2 (5 * 32) + 2 * c23 * pow2 (6 * 32)) canon;

  let a_ = c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32) in 
  let c12_ = c12 + c12 * pow2 (3 * 32) + c12 * pow2 (4 * 32)  - c12 * pow2 32 in 
  let c13_ = c13 * pow2 32 + c13 * pow2 (4 * 32) + c13 * pow2 (5 * 32) - c13 * pow2(2 *32) in 
  let c14_ = c14 * pow2 (2 * 32) + c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) - c14 * pow2 (3 * 32) in 
  let c15_ = c15 * pow2 (3 * 32) + c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) - c15 * pow2 (4 * 32) in 
  let c16_ = c16 * pow2 (4 * 32) + c16 * pow2 (7 * 32) + c16 * pow2 (8 * 32) - c16 * pow2 (5 * 32) in 
  let c17_ = c17 * pow2 (5 * 32) + c17 * pow2 (8 * 32) + c17 * pow2 (9 * 32) - c17 * pow2 (6 * 32) in 
  let c18_ = c18 * pow2 (6 * 32) + c18 * pow2 (9 * 32) + c18 * pow2 (10 * 32) - c18 * pow2 (7 * 32) in 
  let c19_ = c19 * pow2 (7 * 32) + c19 * pow2 (10 * 32) + c19 * pow2 (11 * 32) - c19 * pow2 (8 * 32) in 
  let c20_ = c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 32 in 
  let c21_ = 2 * c21 * pow2 (4 * 32) + c21 * pow2 (9 * 32) + c21 + c21 * pow2 (5 * 32) + c21 * pow2 (3 * 32) - c21 * pow2 (2 * 32) - c21 * pow2 (10 * 32) in 
  let c22_ = 2 * c22 * pow2 (5 * 32) + c22 * pow2 (10 * 32) + c22 * pow2 32 + c22 * pow2 (6 * 32) + c22 * pow2 (4 * 32) - c22 * pow2 (11 * 32) - c22 * pow2 (3 * 32) in 
  let c23_ = 2 * c23 * pow2 (6 * 32) + c23 * pow2 (11 * 32) + c23 * pow2 (2 * 32) + c23 * pow2 32 + c23 * pow2 (7 * 32) + c23 * pow2 (5 * 32) - c23 - c23 * pow2 (4 * 32) - c23 * pow2 (3 * 32) - c23 * pow2 (4 * 32) in 
    
  inside_mod a_ c12_ c13_ c14_ c15_ c16_ c17_ c18_ c19_ c20_ c21_ c22_ c23_;
  
  c12_reduction c12;
    c13_reduction c13;
      c14_reduction c14;
	c15_reduction c15;
  
  c16_reduction c16;
    c17_reduction c17;
      c18_reduction c18;
	c19_reduction c19;
 
  c20_reduction c20;
    c21_reduction c21;
      c22_reduction c22;
	c23_reduction c23;

  inside_mod a_ (c12 * pow2 (12 * 32)) (c13 * pow2 (13 * 32)) (c14 * pow2 (14 * 32)) (c15 * pow2 (15 * 32)) (c16 * pow2 (16 * 32)) (c17 * pow2 (17 * 32)) (c18 * pow2 (18 * 32)) (c19 * pow2 (19 * 32)) (c20 * pow2 (20 * 32)) (c21 * pow2 (21 * 32))  (c22 * pow2 (22 * 32)) (c23 * pow2 (23 * 32))
