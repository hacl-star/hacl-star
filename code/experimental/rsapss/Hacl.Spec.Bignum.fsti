module Hacl.Spec.Bignum

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions

module BSeq = Lib.ByteSequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_add: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> carry & lbignum aLen

val bn_add_lemma: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (let (c_out, res) = bn_add a b in bn_v res + v c_out * pow2 (64 * aLen) == bn_v a + bn_v b)


val bn_sub: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> carry & lbignum aLen

val bn_sub_lemma: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (let (c_out, res) = bn_sub a b in bn_v res - v c_out * pow2 (64 * aLen) == bn_v a - bn_v b)


val bn_mul: #aLen:size_nat -> #bLen:size_nat{aLen + bLen <= max_size_t} -> a:lbignum aLen -> b:lbignum bLen -> lbignum (aLen + bLen)

val bn_mul_lemma: #aLen:size_nat -> #bLen:size_nat{aLen + bLen <= max_size_t} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (bn_v (bn_mul a b) == bn_v a * bn_v b)


val bn_mul1_lshift_add:
    #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum aLen
  -> b:uint64
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum resLen ->
  uint64 & lbignum resLen

//eval_ resLen res (aLen + j) == bn_v (sub res 0 (aLen + j))
val bn_mul1_lshift_add_lemma:
    #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum aLen
  -> b:uint64
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum resLen ->
  Lemma (let (c_out, res) = bn_mul1_lshift_add a b j acc in
    v c_out * pow2 (64 * (aLen + j)) + eval_ resLen res (aLen + j) ==
    eval_ resLen acc (aLen + j) + bn_v a * v b * pow2 (64 * j))


val bn_rshift: #len:size_nat -> b:lbignum len -> i:size_nat{i < len} -> lbignum (len - i)

val bn_rshift_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i < len} ->
  Lemma (bn_v (bn_rshift b i) == bn_v b / pow2 (64 * i))


val bn_sub_mask: #len:size_nat -> n:lbignum len -> a:lbignum len -> lbignum len

val bn_sub_mask_lemma: #len:size_nat -> n:lbignum len -> a:lbignum len -> Lemma
  (requires bn_v a <= bn_v n)
  (ensures  bn_v (bn_sub_mask n a) == (if bn_v a = bn_v n then 0 else bn_v a))


///
///  Get and set i-th bit of a bignum
///

val bn_is_bit_set: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> bool

val bn_is_bit_set_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} ->
  Lemma (bn_is_bit_set b i == (bn_v b / pow2 i % 2 = 1))

val bn_bit_set: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> lbignum len

val bn_bit_set_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> Lemma
  (requires bn_v b < pow2 i)
  (ensures  bn_v (bn_bit_set b i) == bn_v b + pow2 i)

///
///  Conversion functions for bignum
///

val bn_from_bytes_be: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len -> lbignum (blocks len 8)

val bn_from_bytes_be_lemma: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_be len b) == BSeq.nat_from_bytes_be b)


val bn_to_bytes_be:
    len:size_pos{8 * (blocks len 8) <= max_size_t}
  -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} ->
  lseq uint8 len

val bn_to_bytes_be_lemma:
    len:size_pos{8 * (blocks len 8) <= max_size_t}
  -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_be len b == BSeq.nat_to_intseq_be #U8 len (bn_v b))
