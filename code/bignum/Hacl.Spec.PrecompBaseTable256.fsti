module Hacl.Spec.PrecompBaseTable256

open FStar.Mul
open Lib.IntTypes

module LSeq = Lib.Sequence
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mod_pow2_sub: x:nat -> a:nat -> b:nat ->
  Lemma (x / pow2 a % pow2 b * pow2 a == x % pow2 (a + b) - x % pow2 a)

let decompose_nat256_as_four_u64 (x:nat{x < pow2 256}) =
  let x0 = x % pow2 64 in
  let x1 = x / pow2 64 % pow2 64 in
  let x2 = x / pow2 128 % pow2 64 in
  let x3 = x / pow2 192 % pow2 64 in
  (x0, x1, x2, x3)

val lemma_decompose_nat256_as_four_u64: x:nat{x < pow2 256} ->
  Lemma (let (x0, x1, x2, x3) = decompose_nat256_as_four_u64 x in
    x0 + x1 * pow2 64 + x2 * pow2 128 + x3 * pow2 192 == x)

// TODO?: define this function for any b
let exp_as_exp_four_nat256_precomp (#t:Type) (k:LE.comm_monoid t) (a:t) (b:nat{b < pow2 256}) =
  let (b0, b1, b2, b3) = decompose_nat256_as_four_u64 b in
  let a_pow2_64 = LE.pow k a (pow2 64) in
  let a_pow2_128 = LE.pow k a (pow2 128) in
  let a_pow2_192 = LE.pow k a (pow2 192) in
  LE.exp_four_fw k a 64 b0 a_pow2_64 b1 a_pow2_128 b2 a_pow2_192 b3 4

val lemma_point_mul_base_precomp4: #t:Type -> k:LE.comm_monoid t -> a:t -> b:nat{b < pow2 256} ->
  Lemma (exp_as_exp_four_nat256_precomp k a b == LE.pow k a b)

//---------------------------------------

// Loops.repeat b k.sqr a
let rec exp_pow2_rec (#t:Type) (k:SE.concrete_ops t) (a:t) (b:nat) : Tot t (decreases b) =
  if b = 0 then a else k.sqr (exp_pow2_rec k a (b - 1))

val exp_pow2_rec_is_exp_pow2: #t:Type -> k:SE.concrete_ops t -> a:t -> b:nat ->
  Lemma (exp_pow2_rec k a b == SE.exp_pow2 k a b)


let a_pow2_64 (#t:Type) (k:SE.concrete_ops t) (a:t) =
  SE.exp_pow2 k a 64

let a_pow2_128 (#t:Type) (k:SE.concrete_ops t) (a:t) =
  SE.exp_pow2 k (a_pow2_64 k a) 64

let a_pow2_192 (#t:Type) (k:SE.concrete_ops t) (a:t) =
  SE.exp_pow2 k (a_pow2_128 k a) 64


val a_pow2_64_lemma: #t:Type -> k:SE.concrete_ops t -> a:t ->
  Lemma (k.SE.to.SE.refl (a_pow2_64 k a) ==
    LE.pow k.SE.to.SE.comm_monoid (k.SE.to.SE.refl a) (pow2 64))

val a_pow2_128_lemma: #t:Type -> k:SE.concrete_ops t -> a:t ->
  Lemma (k.SE.to.SE.refl (a_pow2_128 k a) ==
    LE.pow k.SE.to.SE.comm_monoid (k.SE.to.SE.refl a) (pow2 128))

val a_pow2_192_lemma: #t:Type -> k:SE.concrete_ops t -> a:t ->
  Lemma (k.SE.to.SE.refl (a_pow2_192 k a) ==
    LE.pow k.SE.to.SE.comm_monoid (k.SE.to.SE.refl a) (pow2 192))

val lemma_decompose_nat256_as_four_u64_lbignum: x:BD.lbignum U64 4{BD.bn_v x < pow2 256} ->
  Lemma (let (x0, x1, x2, x3) = decompose_nat256_as_four_u64 (BD.bn_v x) in
    BD.bn_v (LSeq.sub x 0 1) == x0 /\
    BD.bn_v (LSeq.sub x 1 1) == x1 /\
    BD.bn_v (LSeq.sub x 2 1) == x2 /\
    BD.bn_v (LSeq.sub x 3 1) == x3)
