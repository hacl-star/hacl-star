module Hacl.Spec.Curve25519.Field64.Lemmas

open FStar.Mul

open Lib.Sequence
open Lib.IntTypes

open Spec.Curve25519
open Hacl.Spec.Curve25519.Field64.Definition

module BSeq = Lib.ByteSequence
module SD = Hacl.Spec.Bignum.Definitions
module SL = Hacl.Spec.Bignum.Lib

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_prime: unit -> Lemma (pow2 256 % prime == 38)
let lemma_prime () =
  calc (==) {
    pow2 256 % prime;
    (==) { Math.Lemmas.pow2_plus 255 1 }
    2 * pow2 255 % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 255) prime }
    2 * (pow2 255 % prime) % prime;
    (==) { Math.Lemmas.sub_div_mod_1 (pow2 255) prime }
    2 * (19 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r 2 19 prime }
    38 % prime;
    (==) { Math.Lemmas.small_mod 38 prime }
    38;
    }


val lemma_prime19: unit -> Lemma (pow2 255 % prime == 19)
let lemma_prime19 () =
  assert_norm (pow2 255 % prime = 19 % prime);
  FStar.Math.Lemmas.small_mod 19 prime


val lemma_mul_pow256_add: fn:int -> c:int ->
  Lemma ((fn + c * pow2 256) % prime == (fn + c * 38) % prime)
let lemma_mul_pow256_add fn c =
  calc (==) {
    (fn + c * pow2 256) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * pow2 256) prime }
    (fn + c * pow2 256 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r c (pow2 256) prime }
    (fn + c * (pow2 256 % prime) % prime) % prime;
    (==) { lemma_prime () }
    (fn + c * 38 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * 38) prime }
    (fn + c * 38) % prime;
    }


val lemma_mul_pow255_add: fn:int -> c:int ->
  Lemma ((fn + c * pow2 255) % prime == (fn + c * 19) % prime)
let lemma_mul_pow255_add fn c =
  calc (==) {
    (fn + c * pow2 255) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * pow2 255) prime }
    (fn + c * pow2 255 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r c (pow2 255) prime }
    (fn + c * (pow2 255 % prime) % prime) % prime;
    (==) { lemma_prime19 () }
    (fn + c * 19 % prime) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * 19) prime }
    (fn + c * 19) % prime;
    }


val lemma_fsub4: fn1:nat -> fn2:nat -> c0:nat -> c1:nat ->
  Lemma ((fn1 - fn2 + c0 * pow2 256 - c0 * 38 + c1 * pow2 256 - c1 * 38) % prime ==
    (fn1 % prime - fn2 % prime) % prime)
let lemma_fsub4 fn1 fn2 c0 c1 =
  calc (==) {
    (fn1 - fn2 + c0 * pow2 256 - c0 * 38 + c1 * pow2 256 - c1 * 38) % prime;
    (==) { lemma_mul_pow256_add (fn1 - fn2 + c0 * pow2 256 - c0 * 38 + c1 * pow2 256) (- c1) }
    (fn1 - fn2 + c0 * pow2 256 - c0 * 38 + c1 * pow2 256 - c1 * pow2 256) % prime;
    (==) { }
    (fn1 - fn2 + c0 * pow2 256 - c0 * 38) % prime;
    (==) { lemma_mul_pow256_add (fn1 - fn2 + c0 * pow2 256) (- c0) }
    (fn1 - fn2 + c0 * pow2 256 - c0 * pow2 256) % prime;
    (==) { }
    (fn1 - fn2) % prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l fn1 (- fn2) prime }
    (fn1 % prime - fn2) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (fn1 % prime) fn2 prime }
    (fn1 % prime - fn2 % prime) % prime;
    }


val lemma_mul_lt: a:nat -> b:nat -> c:pos -> d:pos -> Lemma
    (requires a < c /\ b < d)
    (ensures a * b < c * d)
let lemma_mul_lt a b c d = ()


val carry_wide_bound: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires
    a + b * pow2 256 == c + d * 38 /\
    a < pow2 256 /\ c < pow2 256 /\ d < pow2 256)
  (ensures b * 38 < pow2 63)

let carry_wide_bound a b c d =
  assert_norm (38 < pow2 7);
  lemma_mul_lt d 38 (pow2 256) (pow2 7);
  Math.Lemmas.pow2_plus 256 7;
  assert (c + d * 38 < pow2 263);
  Math.Lemmas.pow2_plus 7 7;
  Math.Lemmas.pow2_lt_compat 63 14


val fmul14_bound: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires
    a + b * pow2 256 == c * d /\
    a < pow2 256 /\ c < pow2 256 /\ d < pow2 17)
  (ensures b * 38 < pow2 63)

let fmul14_bound a b c d =
  lemma_mul_lt c d (pow2 256) (pow2 17);
  //Math.Lemmas.pow2_plus 256 17;
  //assert (c * d < pow2 273);
  assert (b < pow2 17);
  assert_norm (38 < pow2 7);
  Math.Lemmas.pow2_plus 17 7;
  Math.Lemmas.pow2_lt_compat 63 24


val carry_pass_store_bound: f:nat -> top_bit:nat -> r0:nat -> r1:nat -> c:nat -> Lemma
  (requires
    top_bit == f / pow2 255 /\
    r0 + top_bit * pow2 255 == f /\
    r1 + c * pow2 256 == r0 + 19 * top_bit /\
    r0 < pow2 256 /\ r1 < pow2 256 /\
    f < pow2 256 /\ top_bit <= 1)
  (ensures c = 0 /\ r0 < pow2 255)

let carry_pass_store_bound f top_bit r0 r1 c = ()


val lemma_subtract_p4_0: f:felem4 -> f':felem4 -> Lemma
  (requires
   (let (f0, f1, f2, f3) = f in
    let (f0', f1', f2', f3') = f' in
    v f3 < pow2 63 /\
    (v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) /\
    (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3)))
  (ensures as_nat4 f' == as_nat4 f % prime)

let lemma_subtract_p4_0 f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  assert_norm (0xffffffffffffffed = pow2 64 - 19);
  assert (as_nat4 f == v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 - 20 + (pow2 64 - 1) * pow2 64 + (pow2 64 - 1) * pow2 64 * pow2 64 +
    (pow2 63 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (as_nat4 f < pow2 255 - 19);
  assert (as_nat4 f == as_nat4 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat4 f') prime


val lemma_subtract_p4_1: f:felem4 -> f':felem4 -> Lemma
  (requires
   (let (f0, f1, f2, f3) = f in
    let (f0', f1', f2', f3') = f' in
    (v f3 = 0x7fffffffffffffff && v f2 = 0xffffffffffffffff && v f1 = 0xffffffffffffffff && v f0 >= 0xffffffffffffffed) /\
    (v f0' = v f0 - 0xffffffffffffffed && v f1' = v f1 - 0xffffffffffffffff && v f2' = v f2 - 0xffffffffffffffff &&
     v f3' = v f3 - 0x7fffffffffffffff)))
  (ensures as_nat4 f' == as_nat4 f % prime)

let lemma_subtract_p4_1 f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  assert_norm (0xffffffffffffffed = pow2 64 - 19);
  assert (as_nat4 f' % prime ==
    (v f0' + v f1' * pow2 64 + v f2' * pow2 64 * pow2 64 + v f3' * pow2 64 * pow2 64 * pow2 64) % prime);
  assert (as_nat4 f' % prime ==
    (v f0 - (pow2 64 - 19) + (v f1 - (pow2 64 - 1)) * pow2 64 + (v f2 - (pow2 64 - 1)) * pow2 64 * pow2 64 +
    (v f3 - (pow2 63 - 1)) * pow2 64 * pow2 64 * pow2 64) % prime);
  assert_norm (pow2 63 * pow2 64 * pow2 64 * pow2 64 = pow2 255);
  assert (as_nat4 f' % prime ==
    (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    v f3 * pow2 64 * pow2 64 * pow2 64 - prime) % prime);
  FStar.Math.Lemmas.lemma_mod_sub
    (v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64) 1 prime


val lemma_subtract_p: f:felem4 -> f':felem4 -> Lemma
  (requires
   (let (f0, f1, f2, f3) = f in
    let (f0', f1', f2', f3') = f' in
    v f3 < pow2 63 /\
    (((v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3)) \/
    ((v f3 = 0x7fffffffffffffff && v f2 = 0xffffffffffffffff && v f1 = 0xffffffffffffffff && v f0 >= 0xffffffffffffffed) /\
      (v f0' = v f0 - 0xffffffffffffffed && v f1' = v f1 - 0xffffffffffffffff && v f2' = v f2 - 0xffffffffffffffff &&
       v f3' = v f3 - 0x7fffffffffffffff)))))
  (ensures as_nat4 f' == as_nat4 f % prime)

let lemma_subtract_p f f' =
  let (f0, f1, f2, f3) = f in
  let (f0', f1', f2', f3') = f' in
  if ((v f3 <> 0x7fffffffffffffff || v f2 <> 0xffffffffffffffff || v f1 <> 0xffffffffffffffff || v f0 < 0xffffffffffffffed) &&
       (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3))
  then lemma_subtract_p4_0 f f'
  else lemma_subtract_p4_1 f f'


val lemma_carry_pass_store_f3: f:lseq uint64 4 ->
  Lemma (let top_bit = f.[3] >>. 63ul in
    let f3' = f.[3] &. u64 0x7fffffffffffffff in
    v top_bit == SD.bn_v f / pow2 255 /\ v top_bit <= 1 /\
    v f3' = v f.[3] % pow2 63 /\
    v f.[3] == v top_bit * pow2 63 + v f3')

let lemma_carry_pass_store_f3 f =
  let top_bit = f.[3] >>. 63ul in
  assert (SL.bn_get_ith_bit f 255 == ((f.[3] >>. 63ul) &. u64 1));
  mod_mask_lemma top_bit 1ul;
  assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1));
  SL.bn_get_ith_bit_lemma f 255;
  assert (v top_bit == SD.bn_v f / pow2 255 % 2);
  SD.bn_eval_bound f 4;
  Math.Lemmas.lemma_div_lt_nat (SD.bn_v f) 256 255;
  Math.Lemmas.small_mod (SD.bn_v f / pow2 255) 2;
  assert (v top_bit == SD.bn_v f / pow2 255);


  let f3' = f.[3] &. u64 0x7fffffffffffffff in
  mod_mask_lemma f.[3] 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert (v (mod_mask #U64 #SEC 63ul) == v (u64 0x7fffffffffffffff));
  assert (v f3' = v f.[3] % pow2 63);
  Math.Lemmas.euclidean_division_definition (v f.[3]) (pow2 63);
  assert (v f.[3] == v top_bit * pow2 63 + v f3');
  assert (v top_bit <= 1)


val lemma_felem64_mod255: a:lseq uint64 4 ->
  Lemma (let r = a.[3] <- (a.[3] &. u64 0x7fffffffffffffff) in
    BSeq.nat_from_intseq_le r == BSeq.nat_from_intseq_le a % pow2 255)

let lemma_felem64_mod255 a =
  lemma_carry_pass_store_f3 a;
  let a3' = a.[3] &. u64 0x7fffffffffffffff in
  assert (v a3' = v a.[3] % pow2 63);

  let r = a.[3] <- a3' in
  SD.bn_upd_eval a a3' 3;
  assert (SD.bn_v r == SD.bn_v a - v a.[3] * pow2 192 + v a3' * pow2 192);

  calc (==) { //SD.bn_v a == SD.bn_v r + v a.[3] * pow2 192 - v a3' * pow2 192
    SD.bn_v r + v a.[3] * pow2 192 - v a3' * pow2 192;
    (==) { }
    SD.bn_v r + v a.[3] * pow2 192 - v a.[3] % pow2 63 * pow2 192;
    (==) { Math.Lemmas.distributivity_sub_left (v a.[3]) (v a.[3] % pow2 63) (pow2 192) }
    SD.bn_v r + (v a.[3] - v a.[3] % pow2 63) * pow2 192;
    (==) { Math.Lemmas.euclidean_division_definition (v a.[3]) (pow2 63) }
    SD.bn_v r + v a.[3] / pow2 63 * pow2 63 * pow2 192;
    (==) { Math.Lemmas.paren_mul_right (v a.[3] / pow2 63) (pow2 63) (pow2 192); Math.Lemmas.pow2_plus 63 192 }
    SD.bn_v r + v a.[3] / pow2 63 * pow2 255;
  };

  Math.Lemmas.modulo_addition_lemma (SD.bn_v r) (pow2 255) (v a.[3] / pow2 63);
  assert (SD.bn_v a % pow2 255 == SD.bn_v r % pow2 255);
  Math.Lemmas.small_mod (SD.bn_v r) (pow2 255);

  Hacl.Spec.Bignum.Convert.bn_v_is_nat_from_intseq_le_lemma 4 r;
  Hacl.Spec.Bignum.Convert.bn_v_is_nat_from_intseq_le_lemma 4 a;
  assert (BSeq.nat_from_intseq_le r == BSeq.nat_from_intseq_le a % pow2 255)
