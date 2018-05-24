module Spec.Bignum.Basic

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas

let bignum bits = n:nat{n < pow2 bits}
let bn_v #n b = b
let bn #n a = a

let bn_cast #n m b = bn #m b

val lemma_bn_add:#n:size_nat -> #m:size_nat{n >= m} -> a:bignum n -> b:bignum m -> Lemma
  (bn_v a + bn_v b < pow2 (n + 1))
let lemma_bn_add #n #m a b = admit()

let bn_add #n #m a b =
  lemma_bn_add #n #m a b;
  bn #(n+1) (a + b)

val lemma_bn_mul:#n:size_nat -> #m:size_nat -> a:bignum n -> b:bignum m -> Lemma
  (bn_v a * bn_v b < pow2 (n + m))
let lemma_bn_mul #n #m a b = admit()
 // assert (bn_v a * bn_v b < pow2 n * pow2 m);

let bn_mul #n #m a b =
  lemma_bn_mul #n #m a b;
  bn #(n+m) (a * b)

let bn_sub #n #m a b = a - b

let bn_get_bit #n b i = (b / pow2 i) % 2
let bn_get_bits #n b i j = (b / pow2 i) % pow2 (j - i)

#reset-options "--z3rlimit 30 --max_fuel 2"
let bn_rshift #n x i =
  assert (x < pow2 n);
  lemma_div_lt x n i;
  x / (pow2 i)

let bn_to_u64 b = u64 b
let bn_from_u64 c = bn #64 (uint_to_nat c)

let bn_is_less #n x y = x < y

val lemma_bn_lshift_mul_add:#n:size_nat -> #m:size_nat -> x:bignum n -> i:size_nat -> y:bignum 64 -> z:bignum m -> Lemma
  (bn_v x * (pow2 i) * bn_v y + bn_v z < pow2 (m + 1))
let lemma_bn_lshift_mul_add #n #m x i y z = admit()

let bn_lshift_mul_add #n #m x i y z =
  lemma_bn_lshift_mul_add #n #m x i y z;
  x * (pow2 i) * y + z

#reset-options "--z3rlimit 50 --max_fuel 0"
let blocks x m = (x - 1) / m + 1

let bn_from_bytes_be #bBits b =
  let res = nat_from_intseq_be b in
  assume (res < pow2 bBits);
  bn #bBits res

let bn_to_bytes_be bBits n =
  assume (bn_v n < pow2 (8 * (blocks bBits 8)));
  nat_to_bytes_be (blocks bBits 8) n

let bn_pow2_r_mod #nBits n r = (pow2 r) % n
