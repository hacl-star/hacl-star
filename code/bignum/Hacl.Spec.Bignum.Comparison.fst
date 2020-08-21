module Hacl.Spec.Bignum.Comparison

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Lib

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Bignum comparison and test functions
///

val bn_is_odd: #len:size_pos -> a:lbignum len -> uint64
let bn_is_odd #len b = b.[0] &. u64 1

val bn_is_odd_lemma: #len:size_pos -> a:lbignum len ->
  Lemma (v (bn_is_odd #len a) == (bn_v a % 2))
let bn_is_odd_lemma #len b =
  bn_eval_split_i #len b 1;
  bn_eval1 (slice b 0 1);
  assert (bn_v b % 2 == (v b.[0] + pow2 64 * bn_v (slice b 1 len)) % 2);
  Math.Lemmas.pow2_plus 1 63;
  Math.Lemmas.modulo_addition_lemma (v b.[0]) 2 (pow2 63 * bn_v (slice b 1 len));
  assert (bn_v b % 2 == v b.[0] % 2);
  mod_mask_lemma b.[0] 1ul;
  assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1))


val bn_eq_mask: #len:size_nat -> a:lbignum len -> b:lbignum len -> uint64
let bn_eq_mask #len a b =
  BSeq.seq_eq_mask a b len

val bn_eq_mask_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len ->
  Lemma (mask_values (bn_eq_mask a b) /\
    (if v (bn_eq_mask a b) = 0 then bn_v a <> bn_v b else bn_v a = bn_v b))
let bn_eq_mask_lemma #len a b =
  let mask = BSeq.seq_eq_mask a b len in
  assert (a == b ==> v mask == v (ones U64 SEC));
  assert (a =!= b ==> v mask == v (zeros U64 SEC));
  Classical.move_requires_2 (bn_eval_inj len) a b


val bn_is_zero_mask: #len:size_nat -> a:lbignum len -> uint64
let bn_is_zero_mask #len b =
  let bn_zero = create len (u64 0) in
  bn_eq_mask b bn_zero

val bn_is_zero_mask_lemma: #len:size_nat -> a:lbignum len ->
  Lemma (mask_values (bn_is_zero_mask #len a) /\
    (if v (bn_is_zero_mask #len a) = 0 then bn_v a <> 0 else bn_v a = 0))
let bn_is_zero_mask_lemma #len b =
  let bn_zero = create len (u64 0) in
  bn_eval_zeroes len len;
  bn_eq_mask_lemma b bn_zero


val bn_lt_mask_f: #len:size_nat -> a:lbignum len -> b:lbignum len -> i:nat{i < len} -> acc:uint64 -> uint64
let bn_lt_mask_f #len a b i acc =
  let beq = eq_mask a.[i] b.[i] in
  let blt = lt_mask a.[i] b.[i] in
  mask_select beq acc (mask_select blt (ones U64 SEC) (zeros U64 SEC))

let bn_lt_mask_t (len:size_nat) (i:nat{i <= len}) = uint64

val bn_lt_mask: #len:size_nat -> a:lbignum len -> b:lbignum len -> uint64
let bn_lt_mask #len a b =
  Loops.repeat_gen len (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0)

val bn_lt_mask_lemma_step:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:pos{k <= len} -> mask0:uint64 -> Lemma
  (requires
    (if v mask0 = 0 then eval_ len a (k - 1) >= eval_ len b (k - 1) else eval_ len a (k - 1) < eval_ len b (k - 1)) /\
    mask_values mask0)
  (ensures (let mask = bn_lt_mask_f #len a b (k - 1) mask0 in
    (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k) /\
    mask_values mask))

let bn_lt_mask_lemma_step #len a b k mask0 =
  let mask = bn_lt_mask_f #len a b (k - 1) mask0 in
  let ai = a.[k - 1] in
  let bi = b.[k - 1] in
  let beq = eq_mask ai bi in
  assert (if v ai = v bi then v beq == v (ones U64 SEC) else v beq == 0);
  let blt = lt_mask ai bi in
  assert (if v ai < v bi then v blt == v (ones U64 SEC) else v blt == 0);

  let res0 = mask_select blt (ones U64 SEC) (zeros U64 SEC) in
  let mask = mask_select beq mask0 res0 in
  //assert (mask == bn_lt_mask_f #len a b (k - 1) mask0);

  mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
  mask_select_lemma beq mask0 res0;

  if v beq = 0 then begin
    assert (v mask = v res0);
    mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
    //assert (v res0 == (if v blt = 0 then 0 else v (ones U64 SEC)));
    assert (if v mask = 0 then v ai > v bi else v ai < v bi);
    if v a.[k - 1] < v b.[k - 1] then bn_eval_lt len a b k else bn_eval_lt len b a k;
    () end
  else begin
    assert (v mask = v mask0);
    //assert (v beq == v (ones U64 SEC));
    //assert (if v mask = v mask0 then v ai = v bi else v ai <> v bi);
    assert (v ai == v bi);
    bn_eval_unfold_i a k;
    bn_eval_unfold_i b k;
    () end


val bn_lt_mask_lemma_loop:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:nat{k <= len} -> Lemma
  (let mask = Loops.repeat_gen k (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0) in
   mask_values mask /\ (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k))

let rec bn_lt_mask_lemma_loop #len a b k =
  let mask = Loops.repeat_gen k (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0) in
  if k = 0 then begin
    Loops.eq_repeat_gen0 k (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0);
    assert (v mask = 0);
    bn_eval0 a;
    bn_eval0 b end
  else begin
    let mask0 = Loops.repeat_gen (k - 1) (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0) in
    Loops.unfold_repeat_gen k (bn_lt_mask_t len) (bn_lt_mask_f #len a b) (u64 0) (k - 1);
    bn_lt_mask_lemma_loop #len a b (k - 1);
    bn_lt_mask_lemma_step #len a b k mask0 end


val bn_lt_mask_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len ->
  Lemma (mask_values (bn_lt_mask a b) /\
    (if v (bn_lt_mask a b) = 0 then bn_v a >= bn_v b else bn_v a < bn_v b))
let bn_lt_mask_lemma #len a b =
  bn_lt_mask_lemma_loop #len a b len


// we could compare bBits with x, but we don't have the bn_num_bits function
val bn_lt_pow2_mask: #len:size_nat -> b:lbignum len -> x:size_nat{x < 64 * len} -> uint64
let bn_lt_pow2_mask #len b x =
  let b2 = create len (u64 0) in
  let b2 = bn_set_ith_bit b2 x in
  bn_lt_mask b b2

val bn_lt_pow2_mask_lemma: #len:size_nat -> b:lbignum len -> x:size_nat{x < 64 * len} ->
  Lemma (mask_values (bn_lt_pow2_mask #len b x) /\
    (if v (bn_lt_pow2_mask #len b x) = 0 then bn_v b >= pow2 x else bn_v b < pow2 x))
let bn_lt_pow2_mask_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  let b2 = create len (u64 0) in
  bn_eval_zeroes len len;
  assert (bn_v b2 = 0);
  //assert (bn_v b2 < pow2 x);
  let b2' = bn_set_ith_bit b2 x in
  bn_set_ith_bit_lemma b2 x;
  assert (bn_v b2' == pow2 x);
  bn_lt_mask_lemma b b2'


val bn_gt_pow2_mask: #len:size_nat -> b:lbignum len -> x:size_nat{x < 64 * len} -> uint64
let bn_gt_pow2_mask #len b x =
  let b2 = create len (u64 0) in
  let b2 = bn_set_ith_bit b2 x in
  bn_lt_mask b2 b

val bn_gt_pow2_mask_lemma: #len:size_nat -> b:lbignum len -> x:size_nat{x < 64 * len} ->
  Lemma (mask_values (bn_gt_pow2_mask #len b x) /\
    (if v (bn_gt_pow2_mask #len b x) = 0 then pow2 x >= bn_v b else pow2 x < bn_v b))
let bn_gt_pow2_mask_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  let b2 = create len (u64 0) in
  bn_eval_zeroes len len;
  assert (bn_v b2 = 0);
  //assert (bn_v b2 < pow2 x);
  let b2' = bn_set_ith_bit b2 x in
  bn_set_ith_bit_lemma b2 x;
  assert (bn_v b2' == pow2 x);
  bn_lt_mask_lemma b2' b
