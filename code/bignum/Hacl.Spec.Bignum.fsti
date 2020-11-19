module Hacl.Spec.Bignum

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions

module BSeq = Lib.ByteSequence


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_add1:
    #t:limb_t
  -> #aLen:size_pos
  -> a:lbignum t aLen
  -> b1:limb t ->
  carry t & lbignum t aLen


val bn_add1_lemma:
    #t:limb_t
  -> #aLen:size_pos
  -> a:lbignum t aLen
  -> b1:limb t ->
  Lemma (let (c, res) = bn_add1 a b1 in
    v c * pow2 (bits t * aLen) + bn_v res == bn_v a + v b1)


val bn_sub1:
    #t:limb_t
  -> #aLen:size_pos
  -> a:lbignum t aLen
  -> b1:limb t ->
  carry t & lbignum t aLen


val bn_sub1_lemma:
    #t:limb_t
  -> #aLen:size_pos
  -> a:lbignum t aLen
  -> b1:limb t ->
  Lemma (let (c, res) = bn_sub1 a b1 in
    bn_v res - v c * pow2 (bits t * aLen) == bn_v a - v b1)


val bn_add:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  carry t & lbignum t aLen


val bn_add_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (let (c_out, res) = bn_add a b in
    bn_v res + v c_out * pow2 (bits t * aLen) == bn_v a + bn_v b)


val bn_sub:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  carry t & lbignum t aLen


val bn_sub_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (let (c_out, res) = bn_sub a b in
    bn_v res - v c_out * pow2 (bits t * aLen) == bn_v a - bn_v b)


val bn_reduce_once:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> c:carry t
  -> a:lbignum t len ->
  lbignum t len


val bn_reduce_once_lemma:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> c:carry t
  -> a:lbignum t len -> Lemma
  (requires v c * pow2 (bits t * len) + bn_v a < 2 * bn_v n)
  (ensures  bn_v (bn_reduce_once n c a) == (v c * pow2 (bits t * len) + bn_v a) % bn_v n)


val bn_add_mod_n:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> a:lbignum t len
  -> b:lbignum t len ->
  lbignum t len


val bn_add_mod_n_lemma:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> a:lbignum t len
  -> b:lbignum t len -> Lemma
  (requires bn_v a < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (bn_add_mod_n n a b) == (bn_v a + bn_v b) % bn_v n)


val bn_mul1:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b1:limb t ->
  limb t & lbignum t aLen


val bn_mul1_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b1:limb t ->
  Lemma (let (c, res) = bn_mul1 a b1 in
    v c * pow2 (bits t * aLen) + bn_v res == bn_v a * v b1)


val bn_mul:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  lbignum t (aLen + bLen)


val bn_mul_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (bn_v (bn_mul a b) == bn_v a * bn_v b)


val bn_karatsuba_mul:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  lbignum t (aLen + aLen)


val bn_karatsuba_mul_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  Lemma (bn_karatsuba_mul a b == bn_mul a b /\
    bn_v (bn_karatsuba_mul a b) == bn_v a * bn_v b)


val bn_sqr:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  lbignum t (aLen + aLen)


val bn_sqr_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  Lemma (bn_sqr a == bn_mul a a /\ bn_v (bn_sqr a) == bn_v a * bn_v a)


val bn_karatsuba_sqr:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  lbignum t (aLen + aLen)


val bn_karatsuba_sqr_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  Lemma (bn_karatsuba_sqr a == bn_mul a a /\
    bn_v (bn_karatsuba_sqr a) == bn_v a * bn_v a)


val bn_mul1_lshift_add:
    #t:limb_t
  -> #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum t aLen
  -> b:limb t
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum t resLen ->
  limb t & lbignum t resLen


//eval_ resLen res (aLen + j) == bn_v (sub res 0 (aLen + j))
val bn_mul1_lshift_add_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum t aLen
  -> b:limb t
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum t resLen ->
  Lemma (let (c_out, res) = bn_mul1_lshift_add a b j acc in
    v c_out * pow2 (bits t * (aLen + j)) + eval_ resLen res (aLen + j) ==
    eval_ resLen acc (aLen + j) + bn_v a * v b * pow2 (bits t * j) /\
    slice res (aLen + j) resLen == slice acc (aLen + j) resLen)


val bn_rshift:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i < len} ->
  lbignum t (len - i)


val bn_rshift_lemma:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i < len} ->
  Lemma (bn_v (bn_rshift b i) == bn_v b / pow2 (bits t * i))


val bn_sub_mask:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> a:lbignum t len ->
  lbignum t len


val bn_sub_mask_lemma:
    #t:limb_t
  -> #len:size_nat
  -> n:lbignum t len
  -> a:lbignum t len -> Lemma
  (requires bn_v a <= bn_v n)
  (ensures  bn_v (bn_sub_mask n a) == (if bn_v a = bn_v n then 0 else bn_v a))


///
///  Get and set i-th bit of a bignum
///

val bn_get_ith_bit:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i / bits t < len} ->
  limb t


val bn_get_ith_bit_lemma:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i / bits t < len} ->
  Lemma (v (bn_get_ith_bit b i) == (bn_v b / pow2 i % 2))


val bn_set_ith_bit:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i / bits t < len} ->
  lbignum t len


val bn_set_ith_bit_lemma:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:size_nat{i / bits t < len} -> Lemma
  (requires bn_v b < pow2 i)
  (ensures  bn_v (bn_set_ith_bit b i) == bn_v b + pow2 i)

///
///  Conditional swap
///

val cswap2:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  tuple2 (lbignum t len) (lbignum t len)


val cswap2_lemma:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t{v bit <= 1}
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  Lemma (let (p1, p2) = cswap2 bit b1 b2 in
    (if v bit = 1 then p1 == b2 /\ p2 == b1 else p1 == b1 /\ p2 == b2))

///
///  Bignum comparison and test functions
///

val bn_is_odd: #t:limb_t -> #len:size_pos -> a:lbignum t len -> limb t

val bn_is_odd_lemma: #t:limb_t -> #len:size_pos -> a:lbignum t len ->
  Lemma (v (bn_is_odd a) == (bn_v a % 2))


val bn_eq_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len -> limb t

val bn_eq_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len ->
  Lemma (mask_values (bn_eq_mask a b) /\
    (if v (bn_eq_mask a b) = 0 then bn_v a <> bn_v b else bn_v a = bn_v b))


val bn_is_zero_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> limb t

val bn_is_zero_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len ->
  Lemma (mask_values (bn_is_zero_mask a) /\
    (if v (bn_is_zero_mask a) = 0 then bn_v a <> 0 else bn_v a = 0))


val bn_lt_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len -> limb t

val bn_lt_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len ->
  Lemma (mask_values (bn_lt_mask a b) /\
    (if v (bn_lt_mask a b) = 0 then bn_v a >= bn_v b else bn_v a < bn_v b))


val bn_lt_pow2_mask: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} -> limb t

val bn_lt_pow2_mask_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} ->
  Lemma (mask_values (bn_lt_pow2_mask b x) /\
    (if v (bn_lt_pow2_mask b x) = 0 then bn_v b >= pow2 x else bn_v b < pow2 x))


val bn_gt_pow2_mask: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} -> limb t

val bn_gt_pow2_mask_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} ->
  Lemma (mask_values (bn_gt_pow2_mask b x) /\
    (if v (bn_gt_pow2_mask b x) = 0 then pow2 x >= bn_v b else pow2 x < bn_v b))

///
///  Conversion functions for bignum
///

val bn_from_uint: #t:limb_t -> len:size_pos -> x:limb t -> lbignum t len

val bn_from_uint_lemma: #t:limb_t -> len:size_pos -> x:limb t ->
  Lemma (bn_v (bn_from_uint len x) == uint_v x)


val bn_from_bytes_be:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lseq uint8 len ->
  lbignum t (blocks len (numbytes t))


val bn_from_bytes_be_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_be #t len b) == BSeq.nat_from_bytes_be b)


val bn_from_bytes_le:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lseq uint8 len ->
  lbignum t (blocks len (numbytes t))


val bn_from_bytes_le_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_le #t len b) == BSeq.nat_from_bytes_le b)


val bn_to_bytes_be:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)) ->
  lseq uint8 len


val bn_to_bytes_be_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_be #t len b == BSeq.nat_to_intseq_be #U8 len (bn_v b))


val bn_to_bytes_le:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)) ->
  lseq uint8 len


val bn_to_bytes_le_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_le len b == BSeq.nat_to_intseq_le #U8 len (bn_v b))
