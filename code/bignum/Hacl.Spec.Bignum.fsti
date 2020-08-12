module Hacl.Spec.Bignum

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions

module BSeq = Lib.ByteSequence


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_add: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> carry & lbignum aLen

val bn_add_lemma: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (let (c_out, res) = bn_add a b in bn_v res + v c_out * pow2 (64 * aLen) == bn_v a + bn_v b)

val bn_sub: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> carry & lbignum aLen

val bn_sub_lemma: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (let (c_out, res) = bn_sub a b in bn_v res - v c_out * pow2 (64 * aLen) == bn_v a - bn_v b)

val bn_reduce_once: #len:size_nat -> n:lbignum len -> c:carry -> a:lbignum len -> lbignum len

val bn_reduce_once_lemma: #len:size_nat -> n:lbignum len -> c:carry -> a:lbignum len -> Lemma
  (requires v c * pow2 (64 * len) + bn_v a < 2 * bn_v n)
  (ensures  bn_v (bn_reduce_once n c a) == (v c * pow2 (64 * len) + bn_v a) % bn_v n)

val bn_add_mod_n: #len:size_nat -> n:lbignum len -> a:lbignum len -> b:lbignum len -> lbignum len

val bn_add_mod_n_lemma: #len:size_nat -> n:lbignum len -> a:lbignum len -> b:lbignum len -> Lemma
  (requires bn_v a < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (bn_add_mod_n n a b) == (bn_v a + bn_v b) % bn_v n)


val bn_mul: #aLen:size_nat -> #bLen:size_nat{aLen + bLen <= max_size_t} -> a:lbignum aLen -> b:lbignum bLen -> lbignum (aLen + bLen)

val bn_mul_lemma: #aLen:size_nat -> #bLen:size_nat{aLen + bLen <= max_size_t} -> a:lbignum aLen -> b:lbignum bLen ->
  Lemma (bn_v (bn_mul a b) == bn_v a * bn_v b)


val bn_sqr: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> lbignum (aLen + aLen)

val bn_sqr_lemma: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen ->
  Lemma (bn_v (bn_sqr a) == bn_v a * bn_v a)


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
    eval_ resLen acc (aLen + j) + bn_v a * v b * pow2 (64 * j) /\
    slice res (aLen + j) resLen == slice acc (aLen + j) resLen)


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
///  Bignum comparison and test functions
///

val bn_is_zero: #len:size_nat -> a:lbignum len -> bool

val bn_is_zero_lemma: #len:size_nat -> a:lbignum len -> Lemma
  (bn_is_zero #len a == (bn_v a = 0))


val bn_is_odd: #len:size_nat -> a:lbignum len -> bool

val bn_is_odd_lemma: #len:size_nat -> a:lbignum len -> Lemma
  (bn_is_odd #len a == (bn_v a % 2 = 1))


val bn_mask_lt: #len:size_nat -> a:lbignum len -> b:lbignum len -> uint64

val bn_mask_lt_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len -> Lemma
  (let mask = bn_mask_lt a b in
   (v mask = 0 \/ v mask = v (ones U64 SEC)) /\
   (if v mask = 0 then bn_v a >= bn_v b else bn_v a < bn_v b))

val bn_is_less: #len:size_nat -> a:lbignum len -> b:lbignum len -> bool

val bn_is_less_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len -> Lemma
  (bn_is_less a b == (bn_v a < bn_v b))


val bn_lt_pow2: #len:size_nat -> b:lbignum len -> x:size_nat -> bool

val bn_lt_pow2_lemma: #len:size_nat -> b:lbignum len -> x:size_nat -> Lemma
  (bn_lt_pow2 #len b x == (bn_v b < pow2 x))

val bn_gt_pow2: #len:size_nat -> b:lbignum len -> x:size_nat -> bool

val bn_gt_pow2_lemma: #len:size_nat -> b:lbignum len -> x:size_nat -> Lemma
  (bn_gt_pow2 #len b x == (pow2 x < bn_v b))

///
///  Conversion functions for bignum
///

val bn_from_uint: len:size_pos -> x:uint64 -> lbignum len

val bn_from_uint_lemma: len:size_pos -> x:uint64 -> Lemma
  (bn_v (bn_from_uint len x) == uint_v x)


val bn_from_bytes_be: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len -> lbignum (blocks len 8)

val bn_from_bytes_be_lemma: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_be len b) == BSeq.nat_from_bytes_be b)


val bn_from_bytes_le: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len -> lbignum (blocks len 8)

val bn_from_bytes_le_lemma: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_le len b) == BSeq.nat_from_bytes_le b)


val bn_to_bytes_be: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lbignum (blocks len 8) -> lseq uint8 len

val bn_to_bytes_be_lemma:
    len:size_pos{8 * (blocks len 8) <= max_size_t}
  -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_be len b == BSeq.nat_to_intseq_be #U8 len (bn_v b))


val bn_to_bytes_le: len:size_pos{8 * (blocks len 8) <= max_size_t} -> b:lbignum (blocks len 8) -> lseq uint8 len

val bn_to_bytes_le_lemma:
    len:size_pos{8 * (blocks len 8) <= max_size_t}
  -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_le len b == BSeq.nat_to_intseq_le #U8 len (bn_v b))
